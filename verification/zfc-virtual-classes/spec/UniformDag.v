From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata UniformSchemata.
From Stdlib Require Import Lists.List Arith.Wf_nat Arith.Compare_dec Lia.
Import ListNotations SetTheory VirtualClasses Schemata UniformSchemata.

(* An abstract representation relation for symbolic formula DAGs. This is
   deliberately independent of the experimental IIL memory layout and hash
   table: it does not assert a refinement of the imperative implementation. *)
Module UniformDag.
Inductive node :=
| NTemplate (p : formula_template)
| NFormula (p : formula)
| NImp (p q : nat)
| NAll (p : nat)
| NGen (p : nat)
| NShift (p : nat)
| NInstantiate (j p : nat)
| NAxiom (a : axiom_template)
| NAxiomPart (a : axiom_template) (side : bool).

Inductive represents (nodes : list node) : nat -> symbolic -> Prop :=
| repr_template i p : nth_error nodes i = Some (NTemplate p) ->
    represents nodes i (sym_template p)
| repr_formula i p : nth_error nodes i = Some (NFormula p) ->
    represents nodes i (sym_formula p)
| repr_imp i l r p q : nth_error nodes i = Some (NImp l r) ->
    represents nodes l p -> represents nodes r q ->
    represents nodes i (sym_imp p q)
| repr_all i l p : nth_error nodes i = Some (NAll l) ->
    represents nodes l p -> represents nodes i (sym_all p)
| repr_gen i l p : nth_error nodes i = Some (NGen l) ->
    represents nodes l p -> represents nodes i (sym_gen p)
| repr_shift i l p : nth_error nodes i = Some (NShift l) ->
    represents nodes l p -> represents nodes i (sym_shift p)
| repr_instantiate i j l p : nth_error nodes i = Some (NInstantiate j l) ->
    represents nodes l p -> represents nodes i (sym_instantiate j p)
| repr_axiom i a : nth_error nodes i = Some (NAxiom a) ->
    represents nodes i (sym_axiom a)
| repr_axiom_part i a side : nth_error nodes i = Some (NAxiomPart a side) ->
    represents nodes i (sym_axiom_part a side).

(* Nodes can be shared freely, but the same ID cannot denote two symbolic
   values, even without assuming acyclicity or collision resistance. *)
Theorem represents_functional nodes i p : represents nodes i p ->
  forall q, represents nodes i q -> p = q.
Proof.
  intros H; induction H; intros s Hs; inversion Hs; subst;
    repeat match goal with
    | H1 : nth_error _ _ = Some _, H2 : nth_error _ _ = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end; try reflexivity; f_equal; eauto.
Qed.

Corollary represented_evaluate_unique nodes i p q rho depth :
  represents nodes i p -> represents nodes i q -> evaluate rho depth p = evaluate rho depth q.
Proof. intros Hp Hq. now rewrite (represents_functional _ _ _ Hp _ Hq). Qed.

Lemma nodup_lookup_unique (nodes : list node) i j n :
  NoDup nodes -> nth_error nodes i = Some n -> nth_error nodes j = Some n -> i = j.
Proof.
  intros Hdistinct Hi Hj. pose proof (proj1 (NoDup_nth_error nodes) Hdistinct) as Hunique.
  apply Hunique; [apply nth_error_Some; congruence|congruence].
Qed.

(* Exact tuple deduplication is enough for symbolic equality to imply ID
   equality. Hashes need not be injective; the arena must compare full nodes. *)
Theorem unique_represented_id nodes : NoDup nodes ->
  forall i p, represents nodes i p -> forall j, represents nodes j p -> i = j.
Proof.
  intros Hdistinct i p H; induction H; intros other Hother; inversion Hother; subst;
    repeat match goal with
    | IH : forall j, represents nodes j ?value -> ?left = j,
      Hr : represents nodes ?right ?value |- _ =>
        let E := fresh in pose proof (IH _ Hr) as E; clear IH; subst
    end;
    eapply nodup_lookup_unique; eassumption.
Qed.

Corollary represented_equality_iff nodes i j p q : NoDup nodes ->
  represents nodes i p -> represents nodes j q -> (i = j <-> p = q).
Proof.
  intros Hdistinct Hi Hj. split.
  - intro E; subst j. eapply represents_functional; eassumption.
  - intro E; subst q. eapply unique_represented_id; eassumption.
Qed.

Definition references_below i n := match n with
  | NImp l r => l < i /\ r < i
  | NAll l | NGen l | NShift l | NInstantiate _ l => l < i
  | _ => True
  end.
Definition ordered nodes := forall i n,
  nth_error nodes i = Some n -> references_below i n.

(* The usual append-only topological discipline guarantees every stored node
   has a finite denotation; no recursive evaluator or termination axiom is
   assumed. *)
Theorem ordered_represents nodes : ordered nodes -> forall i n,
  nth_error nodes i = Some n -> exists p, represents nodes i p.
Proof.
  intros Hordered i. induction i as [i IH] using lt_wf_ind. intros n Hnode.
  assert (Hi : i < length nodes) by (apply nth_error_Some; congruence).
  assert (Hchild : forall j, j < i -> exists p, represents nodes j p).
  { intros j Hj. assert (Hjlen : j < length nodes) by lia.
    destruct (nth_error nodes j) as [child|] eqn:Hlookup.
    - eapply IH; eassumption.
    - apply nth_error_None in Hlookup. lia. }
  pose proof (Hordered i n Hnode) as Hrefs. destruct n; cbn [references_below] in Hrefs.
  - eexists. eapply repr_template. exact Hnode.
  - eexists. eapply repr_formula. exact Hnode.
  - destruct Hrefs as [Hl Hr]. destruct (Hchild _ Hl) as [p Hp].
    destruct (Hchild _ Hr) as [q Hq]. eexists. eapply repr_imp; eassumption.
  - destruct (Hchild _ Hrefs) as [p Hp]. eexists. eapply repr_all; eassumption.
  - destruct (Hchild _ Hrefs) as [p Hp]. eexists. eapply repr_gen; eassumption.
  - destruct (Hchild _ Hrefs) as [p Hp]. eexists. eapply repr_shift; eassumption.
  - destruct (Hchild _ Hrefs) as [p Hp]. eexists. eapply repr_instantiate; eassumption.
  - eexists. eapply repr_axiom. exact Hnode.
  - eexists. eapply repr_axiom_part. exact Hnode.
Qed.

(* The relation remains valid when a node arena grows by appending new nodes. *)
Lemma lookup_append (nodes : list node) i (n : node) : nth_error nodes i = Some n ->
  forall extra, nth_error (nodes ++ extra) i = Some n.
Proof.
  intros H extra. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. congruence.
Qed.

Theorem represents_append nodes i p : represents nodes i p ->
  forall extra, represents (nodes ++ extra) i p.
Proof.
  intro H; induction H; intro extra; eauto using lookup_append, repr_template,
    repr_formula, repr_imp, repr_all, repr_gen, repr_shift, repr_instantiate,
    repr_axiom, repr_axiom_part.
Qed.

(* Numeric fields used by uniform-symbols.js.in. Template and axiom references
   deliberately remain parameters: their actual encodings use additional
   tagged nodes, which must be related to these resolvers separately. This
   partial decoder does not identify arbitrary numeric rows as symbolic nodes. *)
Definition numeric_row := (nat * nat * nat)%type.

(* Structural class and formula-template rows from uniform-symbols.js.in.
   Runtime classes represent abstractions by an interned core formula. *)
Inductive template_resolves (formulas : list formula) (rows : list numeric_row) :
    nat -> formula_template -> Prop :=
| tr_literal i f p : nth_error rows i = Some (42, f, 0) -> nth_error formulas f = Some p ->
    template_resolves formulas rows i (literal_formula p)
| tr_equal i a b x y : nth_error rows i = Some (44, a, b) ->
    class_resolves formulas rows a x -> class_resolves formulas rows b y ->
    template_resolves formulas rows i (template_equal x y)
| tr_member i a b x y : nth_error rows i = Some (45, a, b) ->
    class_resolves formulas rows a x -> class_resolves formulas rows b y ->
    template_resolves formulas rows i (template_member x y)
| tr_imp i a b x y : nth_error rows i = Some (46, a, b) ->
    template_resolves formulas rows a x -> template_resolves formulas rows b y ->
    template_resolves formulas rows i (template_imp x y)
| tr_all i a x : nth_error rows i = Some (47, a, 0) ->
    template_resolves formulas rows a x -> template_resolves formulas rows i (template_all x)
with class_resolves (formulas : list formula) (rows : list numeric_row) :
    nat -> class_template -> Prop :=
| cr_meta i n : nth_error rows i = Some (40, n, 0) ->
    class_resolves formulas rows i (metavariable n)
| cr_set i n : nth_error rows i = Some (41, 0, n) ->
    class_resolves formulas rows i (literal_class (set n))
| cr_literal_abstract i f p : nth_error rows i = Some (41, 1, f) -> nth_error formulas f = Some p ->
    class_resolves formulas rows i (literal_class (abstract (core p)))
| cr_abstract i a p : nth_error rows i = Some (43, a, 0) ->
    template_resolves formulas rows a p -> class_resolves formulas rows i (template_abstract p).

Scheme template_resolves_ind' := Induction for template_resolves Sort Prop
with class_resolves_ind' := Induction for class_resolves Sort Prop.
Combined Scheme structural_resolves_ind from template_resolves_ind', class_resolves_ind'.

Theorem structural_resolves_functional formulas rows :
  (forall i p, template_resolves formulas rows i p ->
    forall q, template_resolves formulas rows i q -> p = q) /\
  (forall i p, class_resolves formulas rows i p ->
    forall q, class_resolves formulas rows i q -> p = q).
Proof.
  apply structural_resolves_ind; intros; match goal with
    | Hr : template_resolves _ _ _ ?rhs |- _ = ?rhs => inversion Hr; subst
    | Hr : class_resolves _ _ _ ?rhs |- _ = ?rhs => inversion Hr; subst
    end;
    repeat match goal with
    | H1 : nth_error _ _ = Some _, H2 : nth_error _ _ = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; clear H2
    end; try reflexivity; f_equal; eauto.
Qed.

(* 15/16 keep both the normalized child used for evaluation and the original
   template and numeric fields used for structural symbolic equality. *)
Inductive axiom_resolves (formulas : list formula) (rows : list numeric_row) :
    nat -> axiom_template -> Prop :=
| ar_part i crow brow trow base tag normalized template p a b c :
    nth_error rows i = Some (34, crow, c) ->
    nth_error rows crow = Some (33, brow, b) ->
    nth_error rows brow = Some (32, trow, a) ->
    nth_error rows trow = Some (31, base, template) ->
    nth_error rows base = Some (30, tag, normalized) ->
    (tag = 15 \/ tag = 16) ->
    template_resolves formulas rows template p ->
    axiom_resolves formulas rows i (template_axiom tag p (literal_formula falsity) (literal_formula falsity) a b c).
Definition decode_symbol (formulas : list formula)
    (template_at : nat -> option formula_template)
    (axiom_at : nat -> option axiom_template) (row : numeric_row) : option node :=
  match row with
  | (0, a, 0) => option_map NFormula (nth_error formulas a)
  | (1, a, 0) => option_map NTemplate (template_at a)
  | (2, a, b) => Some (NImp a b)
  | (3, a, 0) => Some (NAll a)
  | (4, a, 0) => Some (NGen a)
  | (5, a, 0) => Some (NShift a)
  | (6, a, b) => Some (NInstantiate b a)
  | (7, a, 0) => option_map (fun ax => NAxiomPart ax false) (axiom_at a)
  | (7, a, 1) => option_map (fun ax => NAxiomPart ax true) (axiom_at a)
  | _ => None
  end.

Definition numeric_entry formulas template_at axiom_at rows i :=
  match nth_error rows i with
  | Some row => decode_symbol formulas template_at axiom_at row
  | None => None
  end.

Lemma numeric_imp formulas template_at axiom_at rows i a b :
  nth_error rows i = Some (2, a, b) ->
  numeric_entry formulas template_at axiom_at rows i = Some (NImp a b).
Proof. intro H. unfold numeric_entry, numeric_row in *. rewrite H. reflexivity. Qed.

Lemma numeric_instantiate formulas template_at axiom_at rows i child j :
  nth_error rows i = Some (6, child, j) ->
  numeric_entry formulas template_at axiom_at rows i = Some (NInstantiate j child).
Proof. intro H. unfold numeric_entry, numeric_row in *. rewrite H. reflexivity. Qed.

Lemma numeric_axiom_part formulas template_at axiom_at rows i a (side : bool) ax :
  nth_error rows i = Some (7, a, if side then 1 else 0) -> axiom_at a = Some ax ->
  numeric_entry formulas template_at axiom_at rows i = Some (NAxiomPart ax side).
Proof.
  destruct side; intros H Hax; unfold numeric_entry, numeric_row in *;
    rewrite H; cbn [decode_symbol]; now rewrite Hax.
Qed.

Lemma represented_root nodes i p : represents nodes i p ->
  exists n, nth_error nodes i = Some n.
Proof. intro H; inversion H; subst; eauto. Qed.

(* A future machine-level invariant needs this agreement on every reachable ID,
   plus correctness of template_at, axiom_at, and the evaluator's worklist. *)
Definition numeric_agreement formulas template_at axiom_at rows nodes i :=
  forall n, nth_error nodes i = Some n -> numeric_entry formulas template_at axiom_at rows i = Some n.

Theorem represented_numeric_root formulas template_at axiom_at rows nodes i p :
  represents nodes i p -> numeric_agreement formulas template_at axiom_at rows nodes i ->
  exists n, nth_error nodes i = Some n /\ numeric_entry formulas template_at axiom_at rows i = Some n.
Proof. intros Hr Hagree. destruct (represented_root _ _ _ Hr) as [n Hn]. eauto. Qed.

Lemma axiom_resolves_functional formulas rows i a b :
  axiom_resolves formulas rows i a -> axiom_resolves formulas rows i b -> a = b.
Proof.
  intros Ha Hb. inversion Ha; inversion Hb; subst.
  repeat match goal with
  | H1 : nth_error _ _ = Some _, H2 : nth_error _ _ = Some _ |- _ =>
      rewrite H1 in H2; inversion H2; subst; clear H2
  end.
  f_equal. eapply (proj1 (structural_resolves_functional formulas rows)); eassumption.
Qed.

Lemma nodup_lookup_unique_any {A : Type} (xs : list A) i j x :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof.
  intros Hdistinct Hi Hj. pose proof (proj1 (NoDup_nth_error xs) Hdistinct) as Hunique.
  apply Hunique; [apply nth_error_Some; congruence|congruence].
Qed.

(* When structural rows and concrete formula IDs are canonical, equal decoded
   templates/classes have equal IDs. Equality compares full rows; no property
   of the hash function is needed. *)
Theorem structural_resolves_unique_id formulas rows :
  NoDup formulas -> NoDup rows ->
  (forall i p, template_resolves formulas rows i p ->
    forall j, template_resolves formulas rows j p -> i = j) /\
  (forall i p, class_resolves formulas rows i p ->
    forall j, class_resolves formulas rows j p -> i = j).
Proof.
  intros Hform Hrows. apply structural_resolves_ind; intros;
    match goal with
    | |- ?i = ?j =>
      match goal with
      | Hr : template_resolves _ _ j ?p |- _ => inversion Hr; subst
      | Hr : class_resolves _ _ j ?p |- _ => inversion Hr; subst
      end
    end;
    repeat match goal with
    | IH : forall j, template_resolves _ _ j ?p -> ?i = j,
      Hr : template_resolves _ _ ?j ?p |- _ =>
        let E := fresh in pose proof (IH _ Hr) as E; clear IH; subst
    | IH : forall j, class_resolves _ _ j ?p -> ?i = j,
      Hr : class_resolves _ _ ?j ?p |- _ =>
        let E := fresh in pose proof (IH _ Hr) as E; clear IH; subst
    end;
    try match goal with
    | H1 : nth_error formulas ?i = Some ?p,
      H2 : nth_error formulas ?j = Some ?p |- _ =>
        let E := fresh in pose proof (nodup_lookup_unique_any formulas i j p Hform H1 H2) as E; subst
    end;
    eapply nodup_lookup_unique_any; eassumption.
Qed.

(* Direct interpretation of numeric rows, avoiding a separate abstract arena.
   Resolver functions must be supplied together with their own correctness
   invariants; these constructors do not establish IIL execution. *)
Inductive numeric_represents formulas template_at axiom_at rows : nat -> symbolic -> Prop :=
| nr_template i p : numeric_entry formulas template_at axiom_at rows i = Some (NTemplate p) ->
    numeric_represents formulas template_at axiom_at rows i (sym_template p)
| nr_formula i p : numeric_entry formulas template_at axiom_at rows i = Some (NFormula p) ->
    numeric_represents formulas template_at axiom_at rows i (sym_formula p)
| nr_imp i l r p q : numeric_entry formulas template_at axiom_at rows i = Some (NImp l r) ->
    numeric_represents formulas template_at axiom_at rows l p ->
    numeric_represents formulas template_at axiom_at rows r q ->
    numeric_represents formulas template_at axiom_at rows i (sym_imp p q)
| nr_all i l p : numeric_entry formulas template_at axiom_at rows i = Some (NAll l) ->
    numeric_represents formulas template_at axiom_at rows l p ->
    numeric_represents formulas template_at axiom_at rows i (sym_all p)
| nr_gen i l p : numeric_entry formulas template_at axiom_at rows i = Some (NGen l) ->
    numeric_represents formulas template_at axiom_at rows l p ->
    numeric_represents formulas template_at axiom_at rows i (sym_gen p)
| nr_shift i l p : numeric_entry formulas template_at axiom_at rows i = Some (NShift l) ->
    numeric_represents formulas template_at axiom_at rows l p ->
    numeric_represents formulas template_at axiom_at rows i (sym_shift p)
| nr_instantiate i j l p : numeric_entry formulas template_at axiom_at rows i = Some (NInstantiate j l) ->
    numeric_represents formulas template_at axiom_at rows l p ->
    numeric_represents formulas template_at axiom_at rows i (sym_instantiate j p)
| nr_axiom i a : numeric_entry formulas template_at axiom_at rows i = Some (NAxiom a) ->
    numeric_represents formulas template_at axiom_at rows i (sym_axiom a)
| nr_axiom_part i a side : numeric_entry formulas template_at axiom_at rows i = Some (NAxiomPart a side) ->
    numeric_represents formulas template_at axiom_at rows i (sym_axiom_part a side).

Theorem abstract_to_numeric formulas template_at axiom_at rows nodes :
  (forall i, numeric_agreement formulas template_at axiom_at rows nodes i) ->
  forall i p, represents nodes i p -> numeric_represents formulas template_at axiom_at rows i p.
Proof.
  intros Hagree i p H. unfold numeric_agreement in Hagree.
  induction H; eauto 10 using nr_template, nr_formula,
    nr_imp, nr_all, nr_gen, nr_shift, nr_instantiate, nr_axiom, nr_axiom_part.
Qed.

Theorem numeric_to_abstract formulas template_at axiom_at rows nodes :
  (forall i n, numeric_entry formulas template_at axiom_at rows i = Some n ->
     nth_error nodes i = Some n) ->
  forall i p, numeric_represents formulas template_at axiom_at rows i p -> represents nodes i p.
Proof.
  intros Hagree i p H. induction H; eauto 10 using repr_template, repr_formula,
    repr_imp, repr_all, repr_gen, repr_shift, repr_instantiate, repr_axiom, repr_axiom_part.
Qed.
Corollary numeric_represented_equality_iff formulas template_at axiom_at rows nodes i j p q :
  NoDup nodes ->
  (forall k n, numeric_entry formulas template_at axiom_at rows k = Some n ->
     nth_error nodes k = Some n) ->
  numeric_represents formulas template_at axiom_at rows i p ->
  numeric_represents formulas template_at axiom_at rows j q ->
  (i = j <-> p = q).
Proof.
  intros Hdistinct Hagree Hi Hj. eapply represented_equality_iff; [exact Hdistinct| |];
    eapply numeric_to_abstract; eassumption.
Qed.

(* The normalized child in a tag-15/16 key must agree with the structural
   template in the neighboring row. Without this invariant, two distinct keys
   could decode to the same axiom even in a collision-free table. *)
Definition axiom_normalization_coherent formulas rows nodes :=
  forall trow base template tag normal p,
    nth_error rows trow = Some (31, base, template) ->
    nth_error rows base = Some (30, tag, normal) ->
    template_resolves formulas rows template p ->
    represents nodes normal (sym_term p).

Theorem axiom_resolves_unique_id formulas rows nodes :
  NoDup formulas -> NoDup rows -> NoDup nodes ->
  axiom_normalization_coherent formulas rows nodes ->
  forall i ax, axiom_resolves formulas rows i ax ->
  forall j, axiom_resolves formulas rows j ax -> i = j.
Proof.
  intros Hform Hrows Hnodes Hcoherent i ax Hi j Hj.
  unfold axiom_normalization_coherent in Hcoherent.
  inversion Hi as [i1 crow1 brow1 trow1 base1 tag1 norm1 tmpl1 p1 a1 b1 c1
    Hi1 Hcrow1 Hbrow1 Htrow1 Hbase1 Htag1 Htmpl1]; subst ax.
  inversion Hj as [i2 crow2 brow2 trow2 base2 tag2 norm2 tmpl2 p2 a2 b2 c2
    Hi2 Hcrow2 Hbrow2 Htrow2 Hbase2 Htag2 Htmpl2]; subst.
  assert (Etmpl : tmpl1 = tmpl2).
  { eapply (proj1 (structural_resolves_unique_id formulas rows Hform Hrows)); eassumption. }
  subst tmpl2.
  assert (Enorm : norm1 = norm2).
  { assert (Hnorm1 : represents nodes norm1 (sym_term p1))
      by (exact (Hcoherent trow1 base1 tmpl1 tag1 norm1 p1 Htrow1 Hbase1 Htmpl1)).
    assert (Hnorm2 : represents nodes norm2 (sym_term p1))
      by (exact (Hcoherent trow2 base2 tmpl1 tag1 norm2 p1 Htrow2 Hbase2 Htmpl2)).
    eapply unique_represented_id; eassumption. }
  subst norm2.
  assert (Ebase : base1 = base2) by (exact (nodup_lookup_unique_any rows base1 base2 (30,tag1,norm1) Hrows Hbase1 Hbase2)).
  subst base2.
  assert (Etrow : trow1 = trow2) by (exact (nodup_lookup_unique_any rows trow1 trow2 (31,base1,tmpl1) Hrows Htrow1 Htrow2)).
  subst trow2.
  assert (Ebrow : brow1 = brow2) by (exact (nodup_lookup_unique_any rows brow1 brow2 (32,trow1,a1) Hrows Hbrow1 Hbrow2)).
  subst brow2.
  assert (Ecrow : crow1 = crow2) by (exact (nodup_lookup_unique_any rows crow1 crow2 (33,brow1,b1) Hrows Hcrow1 Hcrow2)).
  subst crow2.
  exact (nodup_lookup_unique_any rows i j (34,crow1,c1) Hrows Hi1 Hi2).
Qed.

Lemma lookup_append_any {A : Type} (xs : list A) i x :
  nth_error xs i = Some x -> forall extra, nth_error (xs ++ extra) i = Some x.
Proof.
  intros H extra. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. congruence.
Qed.

(* Appending formulas and tagged rows cannot change previously established
   class or formula-template meanings. *)
Theorem structural_resolves_append formulas rows :
  (forall i p, template_resolves formulas rows i p -> forall fs rs,
     template_resolves (formulas ++ fs) (rows ++ rs) i p) /\
  (forall i p, class_resolves formulas rows i p -> forall fs rs,
     class_resolves (formulas ++ fs) (rows ++ rs) i p).
Proof.
  apply structural_resolves_ind; intros;
    eauto 8 using lookup_append_any, tr_literal, tr_equal, tr_member,
      tr_imp, tr_all, cr_meta, cr_set, cr_literal_abstract, cr_abstract.
Qed.

Theorem axiom_resolves_append formulas rows i a :
  axiom_resolves formulas rows i a -> forall fs rs,
  axiom_resolves (formulas ++ fs) (rows ++ rs) i a.
Proof.
  intros H fs rs. inversion H; subst.
  eapply ar_part; eauto 8 using lookup_append_any.
  eapply (proj1 (structural_resolves_append formulas rows)); eassumption.
Qed.

(* A successful numeric lookup in an existing row is unchanged by extending
   only the symbolic row arena, with the resolvers held fixed. *)
Lemma numeric_entry_append formulas template_at axiom_at rows i n :
  numeric_entry formulas template_at axiom_at rows i = Some n ->
  forall extra, numeric_entry formulas template_at axiom_at (rows ++ extra) i = Some n.
Proof.
  unfold numeric_entry. destruct (nth_error rows i) as [row|] eqn:Hrow; try discriminate.
  intros H extra. rewrite (lookup_append_any rows i row Hrow extra). exact H.
Qed.

Theorem numeric_represents_append_rows formulas template_at axiom_at rows i p :
  numeric_represents formulas template_at axiom_at rows i p -> forall extra,
  numeric_represents formulas template_at axiom_at (rows ++ extra) i p.
Proof.
  intro H. induction H; intro extra; eauto 8 using numeric_entry_append,
    nr_template, nr_formula, nr_imp, nr_all, nr_gen, nr_shift,
    nr_instantiate, nr_axiom, nr_axiom_part.
Qed.

(* Preserve agreement for all existing IDs and establish it for a freshly
   appended ID. The decoded row is an explicit constructor-level premise;
   proving the concrete interner supplies it remains separate. *)
Theorem numeric_agreement_append_one formulas template_at axiom_at rows nodes row n :
  length rows = length nodes ->
  (forall i, numeric_agreement formulas template_at axiom_at rows nodes i) ->
  decode_symbol formulas template_at axiom_at row = Some n ->
  forall i, numeric_agreement formulas template_at axiom_at (rows ++ [row]) (nodes ++ [n]) i.
Proof.
  intros Hlen Hagree Hdecode i m Hnode.
  destruct (lt_dec i (length nodes)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hnode by exact Hlt.
    eapply numeric_entry_append. eapply Hagree. exact Hnode.
  - assert (Hi : i = length nodes).
    { assert (Hbound : i < length (nodes ++ [n])) by (apply nth_error_Some; congruence).
      rewrite length_app in Hbound. cbn in Hbound. lia. }
    subst i. rewrite nth_error_app2 in Hnode by lia.
    replace (length nodes - length nodes) with 0 in Hnode by lia.
    cbn in Hnode. inversion Hnode; subst m.
    unfold numeric_entry. rewrite nth_error_app2 by lia.
    rewrite Hlen. replace (length nodes - length nodes) with 0 by lia.
    exact Hdecode.
Qed.

(* Every existing axiom key keeps its structural template and normalized
   denotation when the three arenas grow by appending. This is a frame result
   for already-present references; coherence of newly added keys still has to
   be shown by the constructor that appends them. *)
Theorem old_axiom_key_coherent_after_append formulas rows nodes trow base template tag normal p :
  axiom_normalization_coherent formulas rows nodes ->
  nth_error rows trow = Some (31, base, template) ->
  nth_error rows base = Some (30, tag, normal) ->
  template_resolves formulas rows template p ->
  forall extra_formulas extra_rows extra_nodes,
    nth_error (rows ++ extra_rows) trow = Some (31, base, template) /\
    nth_error (rows ++ extra_rows) base = Some (30, tag, normal) /\
    template_resolves (formulas ++ extra_formulas) (rows ++ extra_rows) template p /\
    represents (nodes ++ extra_nodes) normal (sym_term p).
Proof.
  intros Hcoherent Htrow Hbase Htemplate fs rs ns.
  unfold axiom_normalization_coherent in Hcoherent.
  repeat split; eauto using lookup_append_any, represents_append.
  eapply (proj1 (structural_resolves_append formulas rows)); eassumption.
Qed.
End UniformDag.
