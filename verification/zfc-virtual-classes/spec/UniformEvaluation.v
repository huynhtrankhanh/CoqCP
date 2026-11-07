From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata UniformSchemata UniformDag.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
Import SetTheory VirtualClasses Schemata UniformSchemata UniformDag.

(* Mathematical model of completing one symbolic worklist entry. A memo maps
   (node, binder depth) to a formula; it is not an IIL execution semantics. *)
Module UniformEvaluation.
Definition memo := nat -> nat -> option formula.
Definition memo_ok (nodes : list node) (rho : nat -> class) (m : memo) :=
  forall i depth p, m i depth = Some p ->
    exists s, represents nodes i s /\ p = evaluate rho depth s.
Definition empty : memo := fun _ _ => None.
Definition put (m : memo) i depth p : memo := fun j d =>
  if Nat.eqb i j && Nat.eqb depth d then Some p else m j d.

Definition finish (nodes : list node) (rho : nat -> class) (m : memo)
    i depth : option formula :=
  match nth_error nodes i with
  | None => None
  | Some (NTemplate p) => Some (instantiate_formula rho depth p)
  | Some (NFormula p) => Some p
  | Some (NImp l r) =>
      match m l depth, m r depth with
      | Some p, Some q => Some (implies p q) | _, _ => None end
  | Some (NAll l) => option_map all (m l depth)
  | Some (NGen l) => option_map all (m l (S depth))
  | Some (NShift l) => option_map shift (m l depth)
  | Some (NInstantiate j l) => option_map (rename (instantiate j)) (m l depth)
  | Some (NAxiom a) => Some (evaluate rho depth (sym_axiom a))
  | Some (NAxiomPart a side) => Some (evaluate rho depth (sym_axiom_part a side))
  end.

Lemma memo_empty_ok nodes rho : memo_ok nodes rho empty.
Proof. intros i depth p H. discriminate. Qed.

Theorem finish_sound nodes rho m i depth p :
  memo_ok nodes rho m -> finish nodes rho m i depth = Some p ->
  exists s, represents nodes i s /\ p = evaluate rho depth s.
Proof.
  intros Hmemo. unfold finish. destruct (nth_error nodes i) as [n|] eqn:Hnode; [|discriminate].
  destruct n as [t|f|l r|l|l|l|j l|a|a side].
  - intro H; inversion H; subst p. exists (sym_template t). split; [now constructor|reflexivity].
  - intro H; inversion H; subst p. exists (sym_formula f). split; [now constructor|reflexivity].
  - destruct (m l depth) as [pl|] eqn:Hl; [|discriminate].
    destruct (m r depth) as [pr|] eqn:Hr; [|discriminate].
    intro H; inversion H; subst p. destruct (Hmemo _ _ _ Hl) as [sl [Hsl El]].
    destruct (Hmemo _ _ _ Hr) as [sr [Hsr Er]].
    exists (sym_imp sl sr). split; [eapply repr_imp; eassumption|cbn; now rewrite <- El, <- Er].
  - destruct (m l depth) as [pl|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst p. destruct (Hmemo _ _ _ Hl) as [sl [Hsl El]].
    exists (sym_all sl). split; [eapply repr_all; eassumption|cbn; now rewrite <- El].
  - destruct (m l (S depth)) as [pl|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst p. destruct (Hmemo _ _ _ Hl) as [sl [Hsl El]].
    exists (sym_gen sl). split; [eapply repr_gen; eassumption|cbn; now rewrite <- El].
  - destruct (m l depth) as [pl|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst p. destruct (Hmemo _ _ _ Hl) as [sl [Hsl El]].
    exists (sym_shift sl). split; [eapply repr_shift; eassumption|cbn; now rewrite <- El].
  - destruct (m l depth) as [pl|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst p. destruct (Hmemo _ _ _ Hl) as [sl [Hsl El]].
    exists (sym_instantiate j sl). split; [eapply repr_instantiate; eassumption|cbn; now rewrite <- El].
  - intro H; inversion H; subst p. exists (sym_axiom a). split; [now constructor|reflexivity].
  - intro H; inversion H; subst p. exists (sym_axiom_part a side). split; [now constructor|reflexivity].
Qed.

Lemma put_ok nodes rho m i depth p : memo_ok nodes rho m ->
  (exists s, represents nodes i s /\ p = evaluate rho depth s) ->
  memo_ok nodes rho (put m i depth p).
Proof.
  intros Hold Hnew j d q. unfold put. destruct (Nat.eqb i j && Nat.eqb depth d) eqn:E.
  - apply andb_true_iff in E as [Ei Ed]. apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ed.
    subst j d. intro H; inversion H; subst q. exact Hnew.
  - apply Hold.
Qed.

Theorem finish_put_ok nodes rho m i depth p : memo_ok nodes rho m ->
  finish nodes rho m i depth = Some p -> memo_ok nodes rho (put m i depth p).
Proof. intros Hm Hfinish. apply put_ok; [exact Hm|exact (finish_sound nodes rho m i depth p Hm Hfinish)]. Qed.

Corollary memo_result_sound nodes rho m i depth p s :
  memo_ok nodes rho m -> represents nodes i s -> m i depth = Some p ->
  p = evaluate rho depth s.
Proof.
  intros Hm Hs Hp. destruct (Hm _ _ _ Hp) as [s' [Hs' E]].
  rewrite (represents_functional _ _ _ Hs' _ Hs) in E. exact E.
Qed.

Definition extends (m n : memo) := forall i d p, m i d = Some p -> n i d = Some p.

Lemma extends_refl m : extends m m.
Proof. intros i d p H. exact H. Qed.

Lemma extends_trans m n o : extends m n -> extends n o -> extends m o.
Proof. intros Hmn Hno i d p H. apply Hno, Hmn, H. Qed.

Lemma put_fresh_extends m i depth p : m i depth = None -> extends m (put m i depth p).
Proof.
  intros Hnone j d q Hq. unfold put.
  destruct (Nat.eqb i j && Nat.eqb depth d) eqn:E; [|exact Hq].
  apply andb_true_iff in E as [Ei Ed]. apply Nat.eqb_eq in Ei. apply Nat.eqb_eq in Ed.
  subst j d. congruence.
Qed.

(* A completed worklist schedule evaluates only entries whose immediate
   children are already memoized. This relation leaves scheduling and memory
   allocation abstract. *)
Inductive completed (nodes : list node) (rho : nat -> class) :
    memo -> list (nat * nat) -> memo -> Prop :=
| completed_nil m : completed nodes rho m nil m
| completed_cons m i depth p tail final :
    finish nodes rho m i depth = Some p ->
    completed nodes rho (put m i depth p) tail final ->
    completed nodes rho m ((i, depth) :: tail)%list final.

Theorem completed_preserves nodes rho m schedule final :
  completed nodes rho m schedule final -> memo_ok nodes rho m -> memo_ok nodes rho final.
Proof.
  intro H. induction H as [m|m i depth p tail final Hfinish Hrun IH]; intro Hmemo; [exact Hmemo|].
  apply IH. eapply finish_put_ok; eassumption.
Qed.

Theorem completed_result nodes rho schedule final i depth p s :
  completed nodes rho empty schedule final ->
  represents nodes i s -> final i depth = Some p -> p = evaluate rho depth s.
Proof.
  intros Hrun Hrepr Hvalue. eapply memo_result_sound; [|exact Hrepr|exact Hvalue].
  eapply completed_preserves; [exact Hrun|apply memo_empty_ok].
Qed.

(* Unlike completed, this relation only writes a previously absent key. *)
Inductive completed_fresh (nodes : list node) (rho : nat -> class) :
    memo -> list (nat * nat) -> memo -> Prop :=
| fresh_nil m : completed_fresh nodes rho m nil m
| fresh_cons m i depth p tail final :
    m i depth = None -> finish nodes rho m i depth = Some p ->
    completed_fresh nodes rho (put m i depth p) tail final ->
    completed_fresh nodes rho m ((i, depth) :: tail)%list final.

Lemma fresh_extends nodes rho m schedule final :
  completed_fresh nodes rho m schedule final -> extends m final.
Proof.
  intro H. induction H as [m|m i depth p tail final Hnone Hfinish Htail IH].
  - apply extends_refl.
  - eapply extends_trans; [apply put_fresh_extends; exact Hnone|exact IH].
Qed.

Lemma fresh_completed nodes rho m schedule final :
  completed_fresh nodes rho m schedule final -> completed nodes rho m schedule final.
Proof.
  intro H. induction H as [m|m i depth p tail final Hnone Hfinish Htail IH].
  - constructor.
  - eapply completed_cons; eassumption.
Qed.

Lemma fresh_append nodes rho m a mid b final :
  completed_fresh nodes rho m a mid -> completed_fresh nodes rho mid b final ->
  completed_fresh nodes rho m (a ++ b)%list final.
Proof.
  intros Ha Hb. induction Ha as [m|m i depth p tail mid Hnone Hfinish Htail IH]; cbn.
  - exact Hb.
  - eapply fresh_cons; [exact Hnone|exact Hfinish|]. apply IH. exact Hb.
Qed.

Lemma put_here m i depth p : put m i depth p i depth = Some p.
Proof. unfold put. now rewrite !Nat.eqb_refl. Qed.

Lemma fresh_preserves nodes rho m schedule final :
  completed_fresh nodes rho m schedule final -> memo_ok nodes rho m -> memo_ok nodes rho final.
Proof. intros Hrun Hmemo. apply fresh_completed in Hrun. eapply completed_preserves; eassumption. Qed.

(* If the children of a node are ready, its evaluation can be completed in at
   most one fresh insertion. An already memoized result is reused. *)
Lemma complete_target nodes rho m i depth s :
  memo_ok nodes rho m -> represents nodes i s ->
  (exists p, finish nodes rho m i depth = Some p) ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s).
Proof.
  intros Hmemo Hrepr [p Hfinish]. destruct (m i depth) as [q|] eqn:Hlookup.
  - exists nil, m. split; [constructor|].
    rewrite <- (memo_result_sound nodes rho m i depth q s Hmemo Hrepr Hlookup). exact Hlookup.
  - assert (Hp : p = evaluate rho depth s).
    { destruct (finish_sound nodes rho m i depth p Hmemo Hfinish) as [s' [Hrepr' Hp]].
      now rewrite (represents_functional _ _ _ Hrepr' _ Hrepr) in Hp. }
    subst p. exists ((i, depth) :: nil)%list, (put m i depth (evaluate rho depth s)).
    split; [eapply fresh_cons; [exact Hlookup|exact Hfinish|constructor]|apply put_here].
Qed.

(* A finite representation derivation determines a finite fresh-insertion
   schedule. This accounts for sharing by reusing already memoized keys. *)
Theorem schedule_exists nodes rho i s : represents nodes i s ->
  forall depth m, memo_ok nodes rho m ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s).
Proof.
  intro H. induction H as
    [i t Hnode|i f Hnode|i l r p q Hnode Hp IHp Hq IHq|
     i l p Hnode Hp IH|i l p Hnode Hp IH|i l p Hnode Hp IH|
     i j l p Hnode Hp IH|i a Hnode|i a side Hnode]; intros depth m Hmemo.
  - eapply complete_target; [exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - eapply complete_target; [exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - destruct (IHp depth m Hmemo) as [sa [ma [Ha Hva]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    destruct (IHq depth ma Hma) as [sb [mb [Hb Hvb]]].
    pose proof (fresh_preserves _ _ _ _ _ Hb Hma) as Hmb.
    assert (Hva' : mb l depth = Some (evaluate rho depth p)).
    { eapply fresh_extends; eassumption. }
    assert (Hrepr : represents nodes i (sym_imp p q)) by (eapply repr_imp; eassumption).
    destruct (complete_target nodes rho mb i depth (sym_imp p q) Hmb Hrepr)
      as [sc [mc [Hc Hresult]]].
    { eexists. unfold finish. rewrite Hnode, Hva', Hvb. reflexivity. }
    exists (sa ++ sb ++ sc)%list, mc. split; [|exact Hresult].
    eapply fresh_append; [exact Ha|]. eapply fresh_append; eassumption.
  - destruct (IH depth m Hmemo) as [sa [ma [Ha Hva]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_all p)) by (eapply repr_all; eassumption).
    destruct (complete_target nodes rho ma i depth (sym_all p) Hma Hrepr)
      as [sb [mb [Hb Hresult]]].
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|exact Hresult].
  - destruct (IH (S depth) m Hmemo) as [sa [ma [Ha Hva]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_gen p)) by (eapply repr_gen; eassumption).
    destruct (complete_target nodes rho ma i depth (sym_gen p) Hma Hrepr)
      as [sb [mb [Hb Hresult]]].
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|exact Hresult].
  - destruct (IH depth m Hmemo) as [sa [ma [Ha Hva]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_shift p)) by (eapply repr_shift; eassumption).
    destruct (complete_target nodes rho ma i depth (sym_shift p) Hma Hrepr)
      as [sb [mb [Hb Hresult]]].
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|exact Hresult].
  - destruct (IH depth m Hmemo) as [sa [ma [Ha Hva]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_instantiate j p)) by (eapply repr_instantiate; eassumption).
    destruct (complete_target nodes rho ma i depth (sym_instantiate j p) Hma Hrepr)
      as [sb [mb [Hb Hresult]]].
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|exact Hresult].
  - eapply complete_target; [exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - eapply complete_target; [exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
Qed.

Lemma fresh_present_not_scheduled nodes rho m schedule final i depth p :
  completed_fresh nodes rho m schedule final -> m i depth = Some p ->
  ~ List.In (i, depth) schedule.
Proof.
  intros Hrun. induction Hrun as [m|m j d q tail final Hnone Hfinish Htail IH]; intros Hpresent Hin.
  - inversion Hin.
  - cbn in Hin. destruct Hin as [E|Hin].
    + inversion E; subst. congruence.
    + apply IH; [|exact Hin]. eapply put_fresh_extends; eassumption.
Qed.

Theorem fresh_schedule_nodup nodes rho m schedule final :
  completed_fresh nodes rho m schedule final -> List.NoDup schedule.
Proof.
  intro Hrun. induction Hrun as [m|m i depth p tail final Hnone Hfinish Htail IH].
  - constructor.
  - constructor; [|exact IH].
    eapply fresh_present_not_scheduled; [exact Htail|apply put_here].
Qed.

(* The number of completed insertions is bounded by any finite set known to
   contain all the scheduled (node, depth) pairs. Establishing a concrete
   machine bound for the IIL stack and helper operations remains separate. *)
Theorem fresh_schedule_bound nodes rho m schedule final universe :
  completed_fresh nodes rho m schedule final ->
  (forall key, List.In key schedule -> List.In key universe) ->
  (length schedule <= length universe)%nat.
Proof.
  intros Hrun Hincl. eapply List.NoDup_incl_length;
    [exact (fresh_schedule_nodup nodes rho m schedule final Hrun)|exact Hincl].
Qed.

Lemma fresh_schedule_node_bound nodes rho m schedule final :
  completed_fresh nodes rho m schedule final ->
  forall i depth, List.In (i, depth) schedule -> (i < length nodes)%nat.
Proof.
  intro Hrun. induction Hrun as [m|m j d q tail final Hnone Hfinish Htail IH]; intros i depth Hin.
  - inversion Hin.
  - cbn in Hin. destruct Hin as [E|Hin].
    + inversion E; subst i depth. unfold finish in Hfinish.
      destruct (nth_error nodes j) as [n|] eqn:Hnode; [|discriminate].
      apply List.nth_error_Some. congruence.
    + eapply IH. exact Hin.
Qed.

(* A concrete bound once a maximum binder depth is known: each node/depth
   pair is inserted at most once. The depth premise is explicit because a
   separate reachability argument is needed to derive it from a root DAG. *)
Theorem fresh_schedule_rectangle_bound nodes rho m schedule final maxdepth :
  completed_fresh nodes rho m schedule final ->
  (forall i depth, List.In (i, depth) schedule -> (depth <= maxdepth)%nat) ->
  (length schedule <= length nodes * S maxdepth)%nat.
Proof.
  intros Hrun Hdepth.
  pose (universe := List.list_prod (List.seq 0 (length nodes)) (List.seq 0 (S maxdepth))).
  assert (Hin : forall key, List.In key schedule -> List.In key universe).
  { intros [i depth] Hkey. unfold universe. apply List.in_prod.
    - apply List.in_seq. pose proof (fresh_schedule_node_bound _ _ _ _ _ Hrun i depth Hkey). lia.
    - apply List.in_seq. pose proof (Hdepth i depth Hkey). lia. }
  pose proof (fresh_schedule_bound _ _ _ _ _ universe Hrun Hin) as Hbound.
  unfold universe in Hbound. rewrite List.length_prod, !List.length_seq in Hbound. exact Hbound.
Qed.

(* The number of enclosing generalizations on a path is an upper bound on
   the increase in substitution depth along that path. *)
Fixpoint depth_span (s : symbolic) : nat :=
  match s with
  | sym_imp p q => Nat.max (depth_span p) (depth_span q)
  | sym_all p | sym_shift p | sym_instantiate _ p => depth_span p
  | sym_gen p => S (depth_span p)
  | _ => 0
  end.

Definition depth_bounded (ceiling : nat) (schedule : list (nat * nat)) :=
  List.Forall (fun key => (snd key <= ceiling)%nat) schedule.

Lemma depth_bounded_weaken schedule a b :
  (a <= b)%nat -> depth_bounded a schedule -> depth_bounded b schedule.
Proof.
  intros Hab H. unfold depth_bounded in *. eapply List.Forall_impl; [|exact H].
  intros [i d]. cbn. lia.
Qed.

Lemma complete_target_bounded nodes rho m i depth s ceiling :
  (depth <= ceiling)%nat -> memo_ok nodes rho m -> represents nodes i s ->
  (exists p, finish nodes rho m i depth = Some p) ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s) /\ depth_bounded ceiling schedule.
Proof.
  intros Hdepth Hmemo Hrepr [p Hfinish]. destruct (m i depth) as [q|] eqn:Hlookup.
  - exists nil, m. repeat split; [constructor| |constructor].
    rewrite <- (memo_result_sound nodes rho m i depth q s Hmemo Hrepr Hlookup). exact Hlookup.
  - assert (Hp : p = evaluate rho depth s).
    { destruct (finish_sound nodes rho m i depth p Hmemo Hfinish) as [s' [Hrepr' Hp]].
      now rewrite (represents_functional _ _ _ Hrepr' _ Hrepr) in Hp. }
    subst p. exists ((i, depth) :: nil)%list, (put m i depth (evaluate rho depth s)).
    repeat split; [eapply fresh_cons; [exact Hlookup|exact Hfinish|constructor]|apply put_here|].
    constructor; [exact Hdepth|constructor].
Qed.

Theorem schedule_exists_bounded nodes rho i s : represents nodes i s ->
  forall depth m, memo_ok nodes rho m ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s) /\
    depth_bounded (depth + depth_span s) schedule.
Proof.
  intro H. induction H as
    [i t Hnode|i f Hnode|i l r p q Hnode Hp IHp Hq IHq|
     i l p Hnode Hp IH|i l p Hnode Hp IH|i l p Hnode Hp IH|
     i j l p Hnode Hp IH|i a Hnode|i a side Hnode]; intros depth m Hmemo.
  - eapply complete_target_bounded; [cbn; lia|exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - eapply complete_target_bounded; [cbn; lia|exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - destruct (IHp depth m Hmemo) as [sa [ma [Ha [Hva Hba]]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    destruct (IHq depth ma Hma) as [sb [mb [Hb [Hvb Hbb]]]].
    pose proof (fresh_preserves _ _ _ _ _ Hb Hma) as Hmb.
    assert (Hva' : mb l depth = Some (evaluate rho depth p)) by (eapply fresh_extends; eassumption).
    assert (Hrepr : represents nodes i (sym_imp p q)) by (eapply repr_imp; eassumption).
    destruct (complete_target_bounded nodes rho mb i depth (sym_imp p q)
        (depth + Nat.max (depth_span p) (depth_span q)))
      as [sc [mc [Hc [Hresult Hbc]]]]; try lia; try assumption.
    { eexists. unfold finish. rewrite Hnode, Hva', Hvb. reflexivity. }
    exists (sa ++ sb ++ sc)%list, mc. split; [|split; [exact Hresult|]].
    + eapply fresh_append; [exact Ha|]. eapply fresh_append; eassumption.
    + cbn [depth_span]. apply List.Forall_app. split.
      * eapply depth_bounded_weaken; [apply Nat.add_le_mono_l, Nat.le_max_l|exact Hba].
      * apply List.Forall_app. split.
        -- eapply depth_bounded_weaken; [apply Nat.add_le_mono_l, Nat.le_max_r|exact Hbb].
        -- exact Hbc.
  - destruct (IH depth m Hmemo) as [sa [ma [Ha [Hva Hba]]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_all p)) by (eapply repr_all; eassumption).
    destruct (complete_target_bounded nodes rho ma i depth (sym_all p) (depth + depth_span p))
      as [sb [mb [Hb [Hresult Hbb]]]]; try lia; try assumption.
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|].
    split; [exact Hresult|]. cbn [depth_span]. apply List.Forall_app. auto.
  - destruct (IH (S depth) m Hmemo) as [sa [ma [Ha [Hva Hba]]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_gen p)) by (eapply repr_gen; eassumption).
    destruct (complete_target_bounded nodes rho ma i depth (sym_gen p) (depth + S (depth_span p)))
      as [sb [mb [Hb [Hresult Hbb]]]]; try lia; try assumption.
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|].
    split; [exact Hresult|]. cbn [depth_span]. apply List.Forall_app. split; [|exact Hbb].
    apply (depth_bounded_weaken sa (S depth + depth_span p) (depth + S (depth_span p))); [lia|exact Hba].
  - destruct (IH depth m Hmemo) as [sa [ma [Ha [Hva Hba]]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_shift p)) by (eapply repr_shift; eassumption).
    destruct (complete_target_bounded nodes rho ma i depth (sym_shift p) (depth + depth_span p))
      as [sb [mb [Hb [Hresult Hbb]]]]; try lia; try assumption.
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|].
    split; [exact Hresult|]. cbn [depth_span]. apply List.Forall_app. auto.
  - destruct (IH depth m Hmemo) as [sa [ma [Ha [Hva Hba]]]].
    pose proof (fresh_preserves _ _ _ _ _ Ha Hmemo) as Hma.
    assert (Hrepr : represents nodes i (sym_instantiate j p)) by (eapply repr_instantiate; eassumption).
    destruct (complete_target_bounded nodes rho ma i depth (sym_instantiate j p) (depth + depth_span p))
      as [sb [mb [Hb [Hresult Hbb]]]]; try lia; try assumption.
    { eexists. unfold finish. rewrite Hnode, Hva. reflexivity. }
    exists (sa ++ sb)%list, mb. split; [eapply fresh_append; eassumption|].
    split; [exact Hresult|]. cbn [depth_span]. apply List.Forall_app. auto.
  - eapply complete_target_bounded; [cbn; lia|exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
  - eapply complete_target_bounded; [cbn; lia|exact Hmemo|econstructor; exact Hnode|].
    eexists. unfold finish. now rewrite Hnode.
Qed.

Theorem schedule_exists_with_bound nodes rho i s : represents nodes i s ->
  forall depth m, memo_ok nodes rho m ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s) /\
    (length schedule <= length nodes * S (depth + depth_span s))%nat.
Proof.
  intros Hrepr depth m Hmemo.
  destruct (schedule_exists_bounded nodes rho i s Hrepr depth m Hmemo)
    as [schedule [final [Hrun [Hresult Hdepth]]]].
  exists schedule, final. split; [exact Hrun|]. split; [exact Hresult|].
  eapply fresh_schedule_rectangle_bound; [exact Hrun|].
  intros j d Hin. unfold depth_bounded in Hdepth.
  rewrite List.Forall_forall in Hdepth. exact (Hdepth (j, d) Hin).
Qed.

(* Every generalization edge descends to a smaller node ID. Thus an ordered
   arena bounds symbolic depth growth by the root ID, even when children are
   shared and the symbolic tree itself is much larger than the DAG. *)
Theorem ordered_depth_span_bound nodes i s :
  ordered nodes -> represents nodes i s -> (depth_span s <= i)%nat.
Proof.
  intros Hordered Hrepr. induction Hrepr as
    [i t Hnode|i f Hnode|i l r p q Hnode Hp IHp Hq IHq|
     i l p Hnode Hp IH|i l p Hnode Hp IH|i l p Hnode Hp IH|
     i j l p Hnode Hp IH|i a Hnode|i a side Hnode]; cbn [depth_span]; try lia.
  - pose proof (Hordered i (NImp l r) Hnode) as Hrefs. cbn [references_below] in Hrefs.
    apply Nat.max_lub; lia.
  - pose proof (Hordered i (NAll l) Hnode) as Hrefs. cbn [references_below] in Hrefs. lia.
  - pose proof (Hordered i (NGen l) Hnode) as Hrefs. cbn [references_below] in Hrefs. lia.
  - pose proof (Hordered i (NShift l) Hnode) as Hrefs. cbn [references_below] in Hrefs. lia.
  - pose proof (Hordered i (NInstantiate j l) Hnode) as Hrefs. cbn [references_below] in Hrefs. lia.
Qed.

Theorem ordered_schedule_exists_with_bound nodes rho i s :
  ordered nodes -> represents nodes i s ->
  forall depth m, memo_ok nodes rho m ->
  exists schedule final, completed_fresh nodes rho m schedule final /\
    final i depth = Some (evaluate rho depth s) /\
    (length schedule <= length nodes * S (depth + i))%nat.
Proof.
  intros Hordered Hrepr depth m Hmemo.
  destruct (schedule_exists_with_bound nodes rho i s Hrepr depth m Hmemo)
    as [schedule [final [Hrun [Hresult Hbound]]]].
  exists schedule, final. split; [exact Hrun|]. split; [exact Hresult|].
  pose proof (ordered_depth_span_bound nodes i s Hordered Hrepr) as Hspan. nia.
Qed.
End UniformEvaluation.
