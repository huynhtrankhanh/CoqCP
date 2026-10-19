From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Bool.Bool.
From Submission Require Import Elimination.
Require Import Trusted.Reference.
Import ListNotations SetTheory VirtualClasses.

Fixpoint infer (s : state) (c : certificate) : option formula :=
  match c with
  | axiom_use a => Some (axiom_formula a)
  | reference n => option_map erase (nth_error s n)
  | modus_ponens ci ca =>
      match infer s ci, infer s ca with
      | Some (implies p q), Some a => if formula_eqb p a then Some q else None
      | _, _ => None
      end
  | generalize c => option_map all (infer s c)
  end.

Definition step (s : state) (c : command) : bool * state :=
  match c with
  | submit p certificate =>
      match infer s certificate with
      | Some q => if formula_eqb q (erase p) then (true, p :: s) else (false, s)
      | None => (false, s)
      end
  | undo => match s with [] => (false, s) | _ :: tail => (true, tail) end
  | reset => (true, [])
  end.

Lemma formula_eqb_spec p q : formula_eqb p q = true <-> p = q.
Proof. unfold formula_eqb. destruct (formula_eq_dec p q); intuition discriminate. Qed.

Theorem infer_sound s c p : infer s c = Some p -> judges s c p.
Proof.
  induction c as [a | n | ci IHi ca IHa | c IH] in p |- *; cbn [infer].
  - intro h. injection h as <-. constructor.
  - destruct (nth_error s n) as [q |] eqn:H; cbn [option_map]; [| discriminate].
    intro h. injection h as <-. now constructor.
  - destruct (infer s ci) as [f |] eqn:Hi; [| discriminate].
    destruct f as [|i j|i j|a b|f]; try discriminate.
    destruct (infer s ca) as [q |] eqn:Ha; [| discriminate].
    destruct (formula_eqb a q) eqn:Heq; [| discriminate].
    apply formula_eqb_spec in Heq. subst q.
    intro h. injection h as <-. eapply j_mp; [apply IHi | apply IHa]; reflexivity.
  - destruct (infer s c) as [q |] eqn:H; cbn [option_map]; [| discriminate].
    intro h. injection h as <-. constructor. apply IH. reflexivity.
Qed.

Theorem infer_complete s c p : judges s c p -> infer s c = Some p.
Proof.
  intro h. induction h as [a | n p Href | ci ca p q Hi IHi Ha IHa | c p Hc IH]; cbn [infer].
  - reflexivity.
  - now rewrite Href.
  - rewrite IHi, IHa. rewrite (proj2 (formula_eqb_spec p p) eq_refl). reflexivity.
  - now rewrite IH.
Qed.

Lemma judges_unique s c p q : judges s c p -> judges s c q -> p = q.
Proof. intros Hp Hq. apply infer_complete in Hp, Hq. congruence. Qed.

Theorem step_exact : exact_step step.
Proof.
  intros s c. destruct c as [p c | |]; cbn [step].
  - destruct (infer s c) as [q |] eqn:Hc.
    + destruct (formula_eqb q (erase p)) eqn:Heq; cbn [fst snd].
      * apply formula_eqb_spec in Heq. subst q. split.
        -- intros _. constructor. now apply infer_sound.
        -- split; [discriminate |]. intros t Ht. inversion Ht; reflexivity.
      * assert (Hbad : forall t, ~ transition s (submit p c) t).
        { intros t Ht. inversion Ht; subst.
          assert (He : q = erase p) by
            (eapply judges_unique; [apply infer_sound; exact Hc | eassumption]).
          apply formula_eqb_spec in He. congruence. }
        split; [discriminate |]. split.
        -- intros _. split; [reflexivity | exact Hbad].
        -- intros t Ht. exfalso. exact (Hbad t Ht).
    + assert (Hbad : forall t, ~ transition s (submit p c) t).
      { intros t Ht. inversion Ht; subst. match goal with
          H : judges _ _ _ |- _ => apply infer_complete in H; congruence end. }
      split; [discriminate |]. split.
      * intros _. split; [reflexivity | exact Hbad].
      * intros t Ht. exfalso. exact (Hbad t Ht).
  - destruct s as [|p s]; cbn [fst snd].
    + split; [discriminate |]. split.
      * intros _. split; [reflexivity |]. intros t Ht. inversion Ht.
      * intros t Ht. inversion Ht.
    + split; [intros _; constructor |]. split; [discriminate |].
      intros t Ht. inversion Ht. reflexivity.
  - cbn [fst snd]. split; [intros _; constructor |]. split; [discriminate |].
    intros t Ht. inversion Ht. reflexivity.
Qed.

Theorem judges_sound s c p : safe s -> judges s c p -> derives p.
Proof.
  intros Hs Hc. induction Hc as [a | n p Href | ci ca p q Hi IHi Ha IHa | c p Hc IH].
  - apply axiom_derivable.
  - apply eliminate. unfold safe in Hs. rewrite Forall_forall in Hs.
    apply Hs. now apply nth_error_In in Href.
  - eapply d_mp; eassumption.
  - now apply d_gen.
Qed.

Theorem transition_safe s c t : safe s -> transition s c t -> safe t.
Proof.
  intros Hs Ht. inversion Ht; subst.
  - constructor; [|exact Hs]. apply conservative. eapply judges_sound; eassumption.
  - inversion Hs; assumption.
  - constructor.
Qed.

Theorem step_safe s c : safe s -> safe (snd (step s c)).
Proof.
  intro Hs. pose proof (step_exact s c) as He.
  destruct (step s c) as [ok t]; cbn [fst snd] in *.
  destruct He as [Ha [Hr Hc]]. destruct ok.
  - eapply transition_safe; [exact Hs | apply Ha; reflexivity].
  - rewrite (proj1 (Hr eq_refl)). exact Hs.
Qed.

Theorem session_safe s cs : safe s -> safe (run step s cs).
Proof.
  intro Hs. induction cs as [|c cs IH] in s, Hs |- *; cbn [run].
  - exact Hs.
  - apply IH, step_safe, Hs.
Qed.

Theorem derives_certificate p : derives p -> forall s, exists c, judges s c p.
Proof.
  intro h. induction h as [p Hax | p q | p q r | p | p j | p q |
    i | i j k | i j k | i j k | p q Hp IHp Hq IHq | p Hp IHp]; intro s.
  - destruct Hax as [| | | | | | phi | phi |].
    + exists (axiom_use Ext). constructor.
    + exists (axiom_use Found). constructor.
    + exists (axiom_use Pair). constructor.
    + exists (axiom_use Union). constructor.
    + exists (axiom_use Power). constructor.
    + exists (axiom_use Infinity). constructor.
    + exists (axiom_use (Separation phi)). constructor.
    + exists (axiom_use (Replacement phi)). constructor.
    + exists (axiom_use Choice). constructor.
  - exists (axiom_use (K p q)). constructor.
  - exists (axiom_use (Srule p q r)). constructor.
  - exists (axiom_use (DNE p)). constructor.
  - exists (axiom_use (Inst p j)). constructor.
  - exists (axiom_use (Dist p q)). constructor.
  - exists (axiom_use (Refl i)). constructor.
  - exists (axiom_use (MemLeft i j k)). constructor.
  - exists (axiom_use (MemRight i j k)). constructor.
  - exists (axiom_use (EqTrans i j k)). constructor.
  - destruct (IHp s) as [ci Hi], (IHq s) as [ca Ha].
    exists (modus_ponens ci ca). eapply j_mp; eassumption.
  - destruct (IHp s) as [c Hc]. exists (generalize c). now constructor.
Qed.

Theorem accepts_every_theorem p :
  proves p -> forall s, exists c, step s (submit p c) = (true, p :: s).
Proof.
  intros Hp s. apply eliminate in Hp.
  destruct (derives_certificate _ Hp s) as [c Hc]. exists c.
  apply (proj2 (proj2 (step_exact s (submit p c)))). now constructor.
Qed.

Theorem reachable_iff_provable p :
  proves p <-> exists cs, In p (run step [] cs).
Proof.
  split.
  - intro Hp. destruct (accepts_every_theorem p Hp []) as [c Hc].
    exists [submit p c]. cbn [run]. rewrite Hc. cbn [snd run]. now left.
  - intros [cs Hcs]. pose proof (session_safe [] cs (Forall_nil _)) as Hsafe.
    unfold safe in Hsafe. rewrite Forall_forall in Hsafe. now apply Hsafe.
Qed.
