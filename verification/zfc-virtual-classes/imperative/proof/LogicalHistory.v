From CoqCP Require Import Options.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import FormulaEncoding.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import list.

Module LogicalHistory.
Definition valid s := forall i fid, nth_error (Protocol.history s) i = Some fid ->
  exists p, Protocol.formula_at s fid = Some p.
Lemma initial_valid : valid Protocol.initial.
Proof. intros i fid H. destruct i; discriminate. Qed.
Lemma extend s t : valid s ->
  (exists extra, Protocol.formulas t = Protocol.formulas s ++ extra) -> Protocol.history t = Protocol.history s -> valid t.
Proof.
  intros Hvalid [extra Hfs] Hhistory i fid Hentry. rewrite Hhistory in Hentry.
  destruct (Hvalid i fid Hentry) as [p Hp]. exists p. unfold Protocol.formula_at in *.
  rewrite Hfs. now apply FormulaEncoding.nth_error_extend.
Qed.
Lemma retained s t : Protocol.retained_storage s t -> valid s -> valid t.
Proof.
  intros [[extra Hfs] [_ [_ [Hhistory _]]]] Hvalid i fid Hentry.
  rewrite Hhistory in Hentry. destruct (Hvalid i fid Hentry) as [p Hp].
  exists p. unfold Protocol.formula_at in *. rewrite Hfs. now apply FormulaEncoding.nth_error_extend.
Qed.
Lemma append_valid s fs cs fid p : valid s -> Protocol.allocation s fs cs fid p ->
  valid (Protocol.State fs cs (Protocol.history s ++ [fid]) (Protocol.bindings s) (Protocol.expressions s)).
Proof.
  intros Hvalid [[extra ->] [_ [Hfid _]]] i entry Hentry. cbn [Protocol.history] in Hentry.
  destruct (Nat.lt_dec i (length (Protocol.history s))) as [Hi|Hi].
  - rewrite nth_error_app1 in Hentry by exact Hi. destruct (Hvalid i entry Hentry) as [q Hq].
    exists q. unfold Protocol.formula_at in *. now apply FormulaEncoding.nth_error_extend.
  - rewrite nth_error_app2 in Hentry by lia.
    destruct (i - length (Protocol.history s)) as [|rest] eqn:Hr; [|destruct rest; discriminate].
    cbn [nth_error] in Hentry. injection Hentry as <-. exists p. exact Hfid.
Qed.
Theorem accepted_valid s q r t : Protocol.accepted s q r t -> valid s -> valid t.
Proof.
  intros Haccept Hvalid. inversion Haccept; subst; try exact Hvalid;
    try solve [eapply extend; [exact Hvalid|exists []; now rewrite app_nil_r|reflexivity]];
    try solve [eapply extend; [exact Hvalid|match goal with H : Protocol.allocation _ _ _ _ _ |- _ => exact (proj1 H) end|reflexivity]].
  - eapply append_valid; eassumption.
  - intros i fid Hentry. cbn [Protocol.with_history Protocol.history] in Hentry.
    apply (Hvalid i fid). match goal with Hfull : Protocol.history s = _ ++ [_] |- _ => rewrite Hfull end.
    now apply FormulaEncoding.nth_error_extend.
  - intros i fid Hentry. destruct i; discriminate.
Qed.
Theorem step_valid s q r t : Protocol.step s q r t -> valid s -> valid t.
Proof.
  intros Hstep Hvalid. inversion Hstep; subst.
  - eapply retained; [eassumption|]. eapply accepted_valid; eassumption.
  - eapply retained; eassumption.
Qed.
Theorem dialogue_valid s qs rs t remaining : Protocol.dialogue s qs rs t remaining -> valid s -> valid t.
Proof.
  intros Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH]; intros Hvalid; try exact Hvalid.
  apply IH. eapply step_valid; eassumption.
Qed.
End LogicalHistory.
