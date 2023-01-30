From stdpp Require Import numbers list.

Lemma foldlSingleton {A B : Type} (f : A -> B -> A) (initial : A) (x : B) : foldl f initial [x] = f initial x.
Proof. easy. Qed.

Lemma foldlMap {A B : Type} (f : A -> B -> A) (g : B -> B) (initial : A) (x : B) (l : list B) : foldl f initial (map g l) = foldl (fun accumulated current => f accumulated (g current)) initial l.
Proof.
  induction l using rev_ind.
  - simpl. reflexivity.
  - rewrite foldl_app, foldlSingleton, map_app, foldl_app. simpl. rewrite <- IHl. reflexivity.
Qed.
