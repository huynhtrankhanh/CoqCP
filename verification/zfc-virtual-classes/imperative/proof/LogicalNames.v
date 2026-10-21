From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata Protocol.
From NativeProof Require Import FormulaEncoding LogicalHistory.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import list.
Module LogicalNames.
Definition denotes s meaning := match meaning with
| Protocol.class_binding id _ => exists cls, Protocol.class_at s id = Some cls
| Protocol.theorem_binding id => exists p, Protocol.formula_at s id = Some p
| Protocol.schema_binding id => exists cert, Protocol.pf s id = Some cert end.
Definition valid s := Forall (fun item => denotes s (snd item)) (Protocol.bindings s).
Lemma initial_valid : valid Protocol.initial.
Proof. constructor. Qed.
Lemma lookup_valid s name meaning : valid s -> Protocol.lookup name (Protocol.bindings s) = Some meaning -> denotes s meaning.
Proof.
  unfold valid. generalize (Protocol.bindings s) as bindings. intros bindings Hvalid.
  induction Hvalid as [|[key value] bindings Hhead Hrest IH]; [discriminate|].
  cbn [Protocol.lookup snd]. destruct (Protocol.name_eq_dec name key); [intro H; injection H as <-; exact Hhead|exact IH].
Qed.
Lemma denotes_extend s t meaning :
  (exists extra, Protocol.formulas t = Protocol.formulas s ++ extra) ->
  (exists extra, Protocol.classes t = Protocol.classes s ++ extra) ->
  (exists extra, Protocol.expressions t = Protocol.expressions s ++ extra) -> denotes s meaning -> denotes t meaning.
Proof.
  intros [fs Hfs] [cs Hcs] [es Hes]. destruct meaning as [id flag|id|id].
  - intros [cls Hcls]. exists cls. unfold Protocol.class_at in *. rewrite Hcs. now apply FormulaEncoding.nth_error_extend.
  - intros [p Hp]. exists p. unfold Protocol.formula_at in *. rewrite Hfs. now apply FormulaEncoding.nth_error_extend.
  - intros [cert Hcert]. exists cert. unfold Protocol.pf in *.
    destruct (nth_error (Protocol.expressions s) id) as [expr|] eqn:Hentry; [destruct expr|]; try discriminate.
    rewrite Hes,(FormulaEncoding.nth_error_extend _ es _ _ Hentry). exact Hcert.
Qed.
Lemma extend s t : valid s ->
  (exists extra, Protocol.formulas t = Protocol.formulas s ++ extra) ->
  (exists extra, Protocol.classes t = Protocol.classes s ++ extra) ->
  (exists extra, Protocol.expressions t = Protocol.expressions s ++ extra) ->
  Protocol.bindings t = Protocol.bindings s -> valid t.
Proof.
  intros Hvalid Hfs Hcs Hes Hbindings. unfold valid in *. rewrite Hbindings.
  eapply Forall_impl; [exact Hvalid|]. intros item Hitem. exact (denotes_extend s t (snd item) Hfs Hcs Hes Hitem).
Qed.
Lemma retained s t : Protocol.retained_storage s t -> valid s -> valid t.
Proof.
  intros [Hfs [_ [Hcs [_ [Hbindings Hes]]]]] Hvalid.
  eapply extend; [exact Hvalid|exact Hfs|exact Hcs|exists []; now rewrite app_nil_r|exact Hbindings].
Qed.
Ltac extends := first [exists []; cbn; now rewrite app_nil_r |eexists; reflexivity
  |match goal with H : Protocol.allocation _ _ _ _ _ |- _ => exact (proj1 H) end
  |match goal with H : Protocol.allocation _ _ _ _ _ |- _ => exact (proj2 (proj2 (proj2 H))) end].
Theorem accepted_valid s q r t : Protocol.accepted s q r t -> valid s -> LogicalHistory.valid s -> valid t.
Proof.
  intros Haccept Hvalid Hhistory. inversion Haccept; subst; try exact Hvalid;
    try solve [eapply extend; [exact Hvalid|extends|extends|extends|reflexivity]].
  - unfold valid in *. cbn [Protocol.bindings]. apply Forall_app. split; [exact Hvalid|].
    constructor; [cbn [snd denotes]; eexists; eassumption|constructor].
  - unfold valid in *. cbn [Protocol.bindings]. apply Forall_app. split; [exact Hvalid|].
    constructor; [cbn [snd denotes]; eapply Hhistory; eassumption|constructor].
  - unfold valid in *. cbn [Protocol.bindings]. apply Forall_app. split; [exact Hvalid|].
    constructor; [cbn [snd denotes]; eexists; eassumption|constructor].
  - unfold valid in *. cbn [Protocol.bindings]. apply Forall_map.
    eapply Forall_impl; [exact Hvalid|]. intros [key meaning] Hmeaning. cbn [fst].
    destruct (Protocol.name_eq_dec _ key); [cbn [snd denotes]; eexists; eassumption|exact Hmeaning].
Qed.
Theorem step_valid s q r t : Protocol.step s q r t -> valid s -> LogicalHistory.valid s -> valid t.
Proof.
  intros Hstep Hvalid Hhistory. inversion Hstep; subst.
  - eapply retained; [eassumption|]. eapply accepted_valid; eassumption.
  - eapply retained; eassumption.
Qed.
Theorem dialogue_valid s qs rs t remaining : Protocol.dialogue s qs rs t remaining -> valid s -> LogicalHistory.valid s -> valid t.
Proof.
  intros Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH]; intros Hvalid Hhistory; try exact Hvalid.
  apply IH; [eapply step_valid|eapply LogicalHistory.step_valid]; eassumption.
Qed.
Theorem initial_dialogue_valid qs rs t remaining : Protocol.dialogue Protocol.initial qs rs t remaining -> valid t.
Proof. intro H. exact (dialogue_valid _ _ _ _ _ H initial_valid LogicalHistory.initial_valid). Qed.
End LogicalNames.
