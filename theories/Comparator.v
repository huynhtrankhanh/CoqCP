From stdpp Require Import numbers list.

(* models the less than operator *)
Structure Comparator (A : Type) := {
  compare : A -> A -> bool;
  transitive : forall a b c, compare a b -> compare b c -> compare a c;
  irreflexive : forall a, ~compare a a;
  asymmetry : forall a b, compare a b -> ~compare b a;
  connected : forall a b, a <> b -> compare a b \/ compare b a;
  equalityExcludedMiddle : forall a b : A, a = b \/ a <> b; (* not true generally *)
}.

Lemma negativelyTransitive {A : Type} (comparator : Comparator A) : forall a b c, ~(compare _ comparator a b) -> ~(compare _ comparator b c) -> ~(compare _ comparator a c).
Proof.
  intros a b c h1 h2 h3.
  pose proof transitive _ comparator a c b h3 as h.
  epose proof connected _ comparator b c _ as h4.
  destruct h4; tauto.
  Unshelve.
  intro h4. rewrite h4 in h1. tauto.
Qed.

Lemma lessThanOrEqual {A : Type} (comparator : Comparator A) : forall a b, ~(compare _ comparator a b) <-> a = b \/ compare _ comparator b a.
Proof.
  intros.
  pose proof connected _ comparator a b.
  split; intros; pose proof equalityExcludedMiddle _ comparator a b as hSplit; pose proof asymmetry _ comparator a b; pose proof irreflexive _ comparator a; pose proof irreflexive _ comparator b; destruct hSplit as [hSplit | hSplit]; try rewrite hSplit; tauto.
Qed.
