From stdpp Require Import numbers list.

(* models the less than operator *)
Structure Comparator (A : Type) := {
  compare : A -> A -> bool;
  transitive : forall a b c, compare a b -> compare b c -> compare a c;
  irreflexive : forall a, ~compare a a;
  asymmetry : forall a b, compare a b -> ~ compare b a;
}.
