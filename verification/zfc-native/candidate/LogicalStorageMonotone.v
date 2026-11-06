From CoqCP Require Import Options.
From Trusted Require Import Protocol Guarantees.
From Stdlib Require Import Lists.List Arith.PeanoNat.
From stdpp Require Import numbers list.

Module LogicalStorageMonotone.
Definition prefix {A} (before after:list A) := exists extra,after=before++extra.
Lemma prefix_refl {A} (xs:list A) : prefix xs xs.
Proof. exists [];now rewrite app_nil_r. Qed.
Lemma prefix_trans {A} (xs ys zs:list A) : prefix xs ys -> prefix ys zs -> prefix xs zs.
Proof. intros [first ->] [second ->]. exists(first++second). now rewrite app_assoc. Qed.
Record extends source after : Prop := Extends {
 formulas : prefix (Protocol.formulas source) (Protocol.formulas after);
 classes : prefix (Protocol.classes source) (Protocol.classes after);
 expressions : prefix (Protocol.expressions source) (Protocol.expressions after)
}.
Lemma reflexive logical : extends logical logical.
Proof. constructor;apply prefix_refl. Qed.
Lemma transitive before middle after : extends before middle -> extends middle after -> extends before after.
Proof. intros [Hfs Hcs Hes] [Hfs' Hcs' Hes'];constructor;eapply prefix_trans;eassumption. Qed.
Theorem accepted source request reply after : Protocol.accepted source request reply after -> extends source after.
Proof.
 intro Haccepted. destruct Haccepted;constructor;
 cbn [Protocol.formulas Protocol.classes Protocol.expressions Protocol.with_history];
 try apply prefix_refl;try (eexists;reflexivity).
 all:match goal with H:Protocol.allocation _ _ _ _ _ |- _=>destruct H as [Hprefix [_ [_ Hclasses]]];assumption end.
Qed.
Theorem retained before after : Protocol.retained_storage before after -> extends before after.
Proof. intros [Hfs [_ [Hcs [_ [_ Hes]]]]]. constructor;[exact Hfs|exact Hcs|rewrite Hes;apply prefix_refl]. Qed.
Theorem step source request reply after : Protocol.step source request reply after -> extends source after.
Proof.
 intro Hstep. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained].
 - eapply transitive;[eapply accepted;exact Haccepted|eapply retained;exact Hretained].
 - now apply retained.
Qed.
Theorem dialogue source requests replies after remaining : Protocol.dialogue source requests replies after remaining -> extends source after.
Proof.
 intro Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH].
 - apply reflexive.
 - apply reflexive.
 - eapply transitive;[eapply step;exact Hstep|exact IH].
Qed.
Lemma formula_lookup before after index formula : extends before after -> Protocol.formula_at before index=Some formula ->
 Protocol.formula_at after index=Some formula.
Proof. intros [Hprefix Hclasses Hexpressions] Hlookup. destruct Hprefix as [extra Hprefix].
 unfold Protocol.formula_at in *. rewrite Hprefix. now apply Guarantees.nth_error_extend. Qed.
Lemma class_lookup before after index cls : extends before after -> Protocol.class_at before index=Some cls ->
 Protocol.class_at after index=Some cls.
Proof. intros [Hformulas Hprefix Hexpressions] Hlookup. destruct Hprefix as [extra Hprefix].
 unfold Protocol.class_at in *. rewrite Hprefix. now apply Guarantees.nth_error_extend. Qed.
Lemma expression_lookup before after index expression : extends before after -> nth_error(Protocol.expressions before)index=Some expression ->
 nth_error(Protocol.expressions after)index=Some expression.
Proof. intros [Hformulas Hclasses [extra Hprefix]] Hlookup. rewrite Hprefix. now apply Guarantees.nth_error_extend. Qed.
End LogicalStorageMonotone.
