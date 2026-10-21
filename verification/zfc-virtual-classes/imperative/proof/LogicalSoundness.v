From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata Protocol.
From NativeProof Require Import FormulaEncoding.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import list.
Module LogicalSoundness.
Import SetTheory.
Lemma axiom_derivable a : derives (axiom_formula a).
Proof. destruct a; cbn [axiom_formula]; constructor; constructor. Qed.
Theorem instance_sound rho depth cert p : Schemata.infer rho depth cert = Some p -> derives p.
Proof.
  induction cert as [a|ci IHi ca IHa|c IH|q Hq] in depth,p |- *; cbn [Schemata.infer].
  - destruct (Schemata.instantiate_axiom rho depth a) as [a'|]; [|discriminate]. cbn [option_map]. intro H. injection H as <-. apply axiom_derivable.
  - destruct (Schemata.infer rho depth ci) as [f|] eqn:Hi; [|discriminate].
    destruct f as [|i j|i j|a b|a]; try discriminate.
    destruct (Schemata.infer rho depth ca) as [f|] eqn:Ha; [|discriminate].
    unfold formula_eqb. destruct (formula_eq_dec a f) as [Hsame|Hdifferent]; [subst f|discriminate].
    intro H. injection H as <-. eapply d_mp; [exact (IHi depth (implies a b) Hi)|exact (IHa depth a Ha)].
  - destruct (Schemata.infer rho (S depth) c) as [q|] eqn:Hc; [|discriminate].
    cbn [option_map]. intro H. injection H as <-. apply d_gen. exact (IH (S depth) q Hc).
  - intro H. injection H as <-. exact Hq.
Qed.
Definition denotes s meaning := match meaning with
| Protocol.class_binding id flag => exists cls, Protocol.class_at s id = Some cls /\ (flag = true -> derives (Protocol.class_setness cls))
| Protocol.theorem_binding id => exists p, Protocol.formula_at s id = Some p /\ derives p
| Protocol.schema_binding id => exists cert, Protocol.pf s id = Some cert end.
Definition history s := forall i fid, nth_error (Protocol.history s) i = Some fid -> exists p, Protocol.formula_at s fid = Some p /\ derives p.
Definition names s := Forall (fun item => denotes s (snd item)) (Protocol.bindings s).
Definition safe s := history s /\ names s.
Lemma initial_safe : safe Protocol.initial.
Proof. split; [intros i fid H; destruct i; discriminate|constructor]. Qed.
Lemma lookup_sound s name meaning : names s -> Protocol.lookup name (Protocol.bindings s) = Some meaning -> denotes s meaning.
Proof.
  unfold names. generalize (Protocol.bindings s) as bindings. intros bindings Hvalid.
  induction Hvalid as [|[key value] bindings Hhead Hrest IH]; [discriminate|].
  cbn [Protocol.lookup snd]. destruct (Protocol.name_eq_dec name key); [intro H; injection H as <-; exact Hhead|exact IH].
Qed.
Lemma theorem_sound s i p : history s -> Protocol.theorem_at s i = Some p -> derives p.
Proof.
  intros Hhistory Htheorem. unfold Protocol.theorem_at in Htheorem.
  destruct (nth_error (Protocol.history s) i) as [fid|] eqn:Hentry; [|discriminate].
  destruct (Hhistory i fid Hentry) as [q [Hq Hderive]]. assert (q = p) by congruence. now subst q.
Qed.
Lemma option_axiom_sound value p : option_map axiom_formula value = Some p -> derives p.
Proof. destruct value as [a|]; [cbn [option_map]; intro H; injection H as <-; apply axiom_derivable|discriminate]. Qed.
Lemma concrete_axiom_sound s tag a b c p : Protocol.concrete_axiom s tag a b c = Some p -> derives p.
Proof.
  unfold Protocol.concrete_axiom. cbn beta zeta.
  repeat match goal with |- context [match ?value with Some _ => _ | None => _ end] => destruct value; [|discriminate] end.
  apply option_axiom_sound.
Qed.
Lemma request_sound s request p : safe s -> Protocol.proof_request s request p -> derives p.
Proof.
  intros [Hhistory Hnames] Hrequest. inversion Hrequest; subst.
  - eapply concrete_axiom_sound; eassumption.
  - eapply d_mp; eapply theorem_sound; eassumption.
  - apply d_gen. eapply theorem_sound; eassumption.
  - eapply theorem_sound; eassumption.
  - match goal with Hlookup : Protocol.lookup _ _ = Some (Protocol.theorem_binding _) |- _ =>
      destruct (lookup_sound s _ _ Hnames Hlookup) as [q [Hq Hderive]] end.
    assert (q = p) by congruence. now subst q.
  - eapply instance_sound; eassumption.
Qed.
Lemma denotes_extend s t meaning :
  (exists extra, Protocol.formulas t = Protocol.formulas s ++ extra) ->
  (exists extra, Protocol.classes t = Protocol.classes s ++ extra) ->
  (exists extra, Protocol.expressions t = Protocol.expressions s ++ extra) -> denotes s meaning -> denotes t meaning.
Proof.
  intros [fs Hfs] [cs Hcs] [es Hes]. destruct meaning as [id flag|id|id].
  - intros [cls [Hcls Hderive]]. exists cls. split; [|exact Hderive]. unfold Protocol.class_at in *. rewrite Hcs. now apply FormulaEncoding.nth_error_extend.
  - intros [p [Hp Hderive]]. exists p. split; [|exact Hderive]. unfold Protocol.formula_at in *. rewrite Hfs. now apply FormulaEncoding.nth_error_extend.
  - intros [cert Hcert]. exists cert. unfold Protocol.pf in *.
    destruct (nth_error (Protocol.expressions s) id) as [expr|] eqn:Hentry; [destruct expr|]; try discriminate.
    rewrite Hes,(FormulaEncoding.nth_error_extend _ es _ _ Hentry). exact Hcert.
Qed.
Lemma extend s t : safe s ->
  (exists extra, Protocol.formulas t = Protocol.formulas s ++ extra) ->
  (exists extra, Protocol.classes t = Protocol.classes s ++ extra) ->
  (exists extra, Protocol.expressions t = Protocol.expressions s ++ extra) ->
  Protocol.history t = Protocol.history s -> Protocol.bindings t = Protocol.bindings s -> safe t.
Proof.
  intros [Hhistory Hnames] Hfs Hcs Hes Hhistoryeq Hbindingseq. split.
  - intros i fid Hentry. rewrite Hhistoryeq in Hentry. destruct (Hhistory i fid Hentry) as [p [Hp Hderive]]. exists p. split; [|exact Hderive].
    unfold Protocol.formula_at in *. destruct Hfs as [extra Hfs]. rewrite Hfs. now apply FormulaEncoding.nth_error_extend.
  - unfold names in *. rewrite Hbindingseq. eapply Forall_impl; [exact Hnames|].
    intros item Hitem. exact (denotes_extend s t (snd item) Hfs Hcs Hes Hitem).
Qed.
Lemma retained s t : Protocol.retained_storage s t -> safe s -> safe t.
Proof.
  intros [Hfs [_ [Hcs [Hhistory [Hbindings Hes]]]]] Hsafe.
  eapply extend; [exact Hsafe|exact Hfs|exact Hcs|exists []; now rewrite app_nil_r|exact Hhistory|exact Hbindings].
Qed.
Lemma append_safe s fs cs fid p : safe s -> Protocol.allocation s fs cs fid p -> derives p ->
  safe (Protocol.State fs cs (Protocol.history s ++ [fid]) (Protocol.bindings s) (Protocol.expressions s)).
Proof.
  intros [Hhistory Hnames] [[extra ->] [_ [Hfid [extra_classes ->]]]] Hderive. split.
  - intros i entry Hentry. cbn [Protocol.history] in Hentry.
    destruct (Nat.lt_dec i (length (Protocol.history s))) as [Hi|Hi].
    + rewrite nth_error_app1 in Hentry by exact Hi. destruct (Hhistory i entry Hentry) as [q [Hq Hqderive]].
      exists q. split; [|exact Hqderive]. unfold Protocol.formula_at in *. now apply FormulaEncoding.nth_error_extend.
    + rewrite nth_error_app2 in Hentry by lia. destruct (i - length (Protocol.history s)) as [|rest] eqn:Hrest; [|destruct rest; discriminate].
      cbn [nth_error] in Hentry. injection Hentry as <-. exists p. split; assumption.
  - unfold names in *. cbn [Protocol.bindings]. eapply Forall_impl; [exact Hnames|]. intros item Hitem.
    eapply denotes_extend; [eexists; reflexivity|eexists; reflexivity|exists []; cbn; now rewrite app_nil_r|exact Hitem].
Qed.
Ltac extends := first [exists []; cbn; now rewrite app_nil_r|eexists; reflexivity
  |match goal with H : Protocol.allocation _ _ _ _ _ |- _ => exact (proj1 H) end
  |match goal with H : Protocol.allocation _ _ _ _ _ |- _ => exact (proj2 (proj2 (proj2 H))) end].
Theorem accepted_safe s q r t : Protocol.accepted s q r t -> safe s -> safe t.
Proof.
  intros Haccept Hsafe. inversion Haccept; subst; try exact Hsafe;
    try solve [eapply extend; [exact Hsafe|extends|extends|extends|reflexivity|reflexivity]].
  - eapply append_safe; [exact Hsafe|eassumption|eapply request_sound; eassumption].
  - split; [exact (proj1 Hsafe)|]. unfold names. cbn [Protocol.bindings]. apply Forall_app. split; [exact (proj2 Hsafe)|].
    constructor; [cbn [snd denotes]; eexists; split; [eassumption|discriminate]|constructor].
  - split; [exact (proj1 Hsafe)|]. unfold names. cbn [Protocol.bindings]. apply Forall_app. split; [exact (proj2 Hsafe)|].
    constructor; [cbn [snd denotes]; eapply (proj1 Hsafe); eassumption|constructor].
  - split; [exact (proj1 Hsafe)|]. unfold names. cbn [Protocol.bindings]. apply Forall_app. split; [exact (proj2 Hsafe)|].
    constructor; [cbn [snd denotes]; eexists; eassumption|constructor].
  - split; [exact (proj1 Hsafe)|]. unfold names. cbn [Protocol.bindings]. apply Forall_map.
    eapply Forall_impl; [exact (proj2 Hsafe)|]. intros [key meaning] Hmeaning. cbn [fst].
    destruct (Protocol.name_eq_dec _ key); [|exact Hmeaning]. cbn [snd denotes]. eexists. split; [eassumption|].
    intros _. eapply theorem_sound; [exact (proj1 Hsafe)|eassumption].
  - split; [|exact (proj2 Hsafe)]. intros i fid Hentry. cbn [Protocol.with_history Protocol.history] in Hentry.
    apply (proj1 Hsafe i fid). match goal with Hfull : Protocol.history s = _ ++ [_] |- _ => rewrite Hfull end.
    now apply FormulaEncoding.nth_error_extend.
  - split; [intros i fid Hentry; destruct i; discriminate|exact (proj2 Hsafe)].
Qed.
Theorem step_safe s q r t : Protocol.step s q r t -> safe s -> safe t.
Proof.
  intros Hstep Hsafe. inversion Hstep; subst.
  - eapply retained; [eassumption|]. eapply accepted_safe; eassumption.
  - eapply retained; eassumption.
Qed.
Theorem dialogue_safe s qs rs t remaining : Protocol.dialogue s qs rs t remaining -> safe s -> safe t.
Proof.
  intros Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH]; intros Hsafe; try exact Hsafe.
  apply IH. eapply step_safe; eassumption.
Qed.
Theorem initial_dialogue_safe qs rs t remaining : Protocol.dialogue Protocol.initial qs rs t remaining -> safe t.
Proof. intro H. exact (dialogue_safe _ _ _ _ _ H initial_safe). Qed.
End LogicalSoundness.
