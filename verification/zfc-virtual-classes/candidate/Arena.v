From CoqCP Require Import Options SetTheory.
From Submission Require Import Elimination.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations SetTheory.

(* A mathematical model of the imperative DAG arena. This is a refinement
   target, not a claim that the generated Action has been proved to refine it. *)
Module Arena.
Inductive node :=
| bottom | eq_node (i j : nat) | mem_node (i j : nat)
| imp_node (left right : nat) | all_node (body : nat).
Definition node_eq_dec : forall a b : node, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition decode_node (meaning : list formula) (n : node) : option formula :=
  match n with
  | bottom => Some falsity
  | eq_node i j => Some (equal i j)
  | mem_node i j => Some (member i j)
  | imp_node i j =>
      match nth_error meaning i, nth_error meaning j with
      | Some p, Some q => Some (implies p q)
      | _, _ => None
      end
  | all_node i => option_map all (nth_error meaning i)
  end.

Record t := { nodes : list node; meaning : list formula }.
Definition represents (a : t) :=
  Forall2 (fun n p => decode_node (meaning a) n = Some p) (nodes a) (meaning a).
Definition initial := {| nodes := [bottom]; meaning := [falsity] |}.
Lemma initial_represents : represents initial.
Proof. repeat constructor. Qed.

Fixpoint find_node n ns : option nat :=
  match ns with
  | [] => None
  | x :: xs => if node_eq_dec n x then Some 0 else option_map S (find_node n xs)
  end.
Lemma find_node_sound n ns i : find_node n ns = Some i -> nth_error ns i = Some n.
Proof.
  induction ns as [| x xs IH] in i |- *; cbn [find_node]; [discriminate |].
  destruct (node_eq_dec n x) as [<- | Hneq].
  - intro H. injection H as <-. reflexivity.
  - destruct (find_node n xs) as [j |] eqn:Hj; cbn [option_map]; [|discriminate].
    intro H. injection H as <-. cbn [nth_error]. now apply IH.
Qed.
Lemma find_node_absent n ns : find_node n ns = None -> ~ In n ns.
Proof.
  induction ns as [| x xs IH]; cbn [find_node]; [tauto |].
  destruct (node_eq_dec n x) as [Heq | Hneq]; [discriminate |].
  destruct (find_node n xs) as [j |] eqn:Hj; cbn [option_map]; [discriminate |].
  intros _ [Heq | Hin]; [congruence |]. exact (IH eq_refl Hin).
Qed.

Lemma nth_error_extend {A} (xs ys : list A) i x :
  nth_error xs i = Some x -> nth_error (xs ++ ys) i = Some x.
Proof.
  intro H. rewrite nth_error_app1; [exact H |].
  apply nth_error_Some. congruence.
Qed.
Lemma decode_extend xs ys n p :
  decode_node xs n = Some p -> decode_node (xs ++ ys) n = Some p.
Proof.
  destruct n as [|i j|i j|left right|body]; cbn [decode_node]; try tauto.
  - destruct (nth_error xs left) as [q |] eqn:Hl; [|discriminate].
    destruct (nth_error xs right) as [r |] eqn:Hr; [|discriminate].
    rewrite (nth_error_extend _ ys _ _ Hl), (nth_error_extend _ ys _ _ Hr). tauto.
  - destruct (nth_error xs body) as [q |] eqn:Hq; [|discriminate].
    rewrite (nth_error_extend _ ys _ _ Hq). tauto.
Qed.

Lemma related_lookup {A B} (R : A -> B -> Prop) xs ys i x :
  Forall2 R xs ys -> nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ R x y.
Proof.
  intro H. induction H as [| z y xs ys Hxy Hxs IH] in i |- *.
  - destruct i; discriminate.
  - destruct i as [| i]; cbn [nth_error].
    + intro Heq. injection Heq as <-. exists y. auto.
    + exact (IH i).
Qed.
Lemma represented_lookup a i n : represents a -> nth_error (nodes a) i = Some n ->
  exists p, nth_error (meaning a) i = Some p /\ decode_node (meaning a) n = Some p.
Proof. apply related_lookup. Qed.

Definition intern (a : t) (n : node) : option (nat * t) :=
  match decode_node (meaning a) n with
  | None => None
  | Some p => match find_node n (nodes a) with
      | Some i => Some (i, a)
      | None => Some (length (nodes a),
          {| nodes := nodes a ++ [n]; meaning := meaning a ++ [p] |})
      end
  end.

Theorem intern_correct a n p : represents a -> decode_node (meaning a) n = Some p ->
  exists i b, intern a n = Some (i, b) /\ represents b /\
    nth_error (meaning b) i = Some p /\
    exists extra, meaning b = meaning a ++ extra.
Proof.
  intros Hrep Hdecode. unfold intern. rewrite Hdecode.
  destruct (find_node n (nodes a)) as [i |] eqn:Hfind.
  - exists i, a. split; [reflexivity |]. split; [exact Hrep |].
    destruct (represented_lookup _ _ _ Hrep (find_node_sound _ _ _ Hfind)) as [q [Hi Hq]].
    rewrite Hdecode in Hq. injection Hq as <-. split; [exact Hi |].
    exists []. now rewrite app_nil_r.
  - exists (length (nodes a)),
      {| nodes := nodes a ++ [n]; meaning := meaning a ++ [p] |}.
    split; [reflexivity |]. cbn [meaning]. split.
    + unfold represents. cbn [nodes meaning]. apply Forall2_app; [|].
      * eapply Forall2_impl; [|exact Hrep]. intros x q Hx. now apply decode_extend.
      * constructor; [now apply decode_extend | constructor].
    + split.
      * rewrite (Forall2_length Hrep), nth_error_app2; [|lia].
        rewrite Nat.sub_diag. reflexivity.
      * exists [p]. reflexivity.
Qed.

Definition safe (a : t) (theorems : list nat) :=
  forall i, In i theorems -> exists p, nth_error (meaning a) i = Some p /\ derives p.
Lemma empty_safe a : safe a [].
Proof. intros i H. inversion H. Qed.

Theorem safe_extend a b proofs extra : meaning b = meaning a ++ extra ->
  safe a proofs -> safe b proofs.
Proof.
  intros He Hsafe i Hin. destruct (Hsafe i Hin) as [p [Hp Hd]].
  exists p. split; [rewrite He; now apply nth_error_extend | exact Hd].
Qed.

Theorem axiom_sound a proofs i witness : safe a proofs ->
  nth_error (meaning a) i = Some (axiom_formula witness) ->
  safe a (i :: proofs).
Proof.
  intros Hsafe Hi j [<- | Hj]; [|now apply Hsafe].
  exists (axiom_formula witness). split; [exact Hi | apply axiom_derivable].
Qed.

Theorem modus_ponens_sound a proofs ci ca result left right :
  safe a proofs -> In ci proofs -> In ca proofs ->
  nth_error (meaning a) ci = Some (implies left right) ->
  nth_error (meaning a) ca = Some left -> nth_error (meaning a) result = Some right ->
  safe a (result :: proofs).
Proof.
  intros Hsafe Hci Hca Himp Harg Hresult j [<- | Hj]; [|now apply Hsafe].
  exists right. split; [exact Hresult |].
  destruct (Hsafe ci Hci) as [p [Hp Hd]]. rewrite Himp in Hp. injection Hp as <-.
  destruct (Hsafe ca Hca) as [q [Hq Hargd]]. rewrite Harg in Hq. injection Hq as <-.
  exact (d_mp left right Hd Hargd).
Qed.

Theorem generalize_sound a proofs source result p :
  safe a proofs -> In source proofs -> nth_error (meaning a) source = Some p ->
  nth_error (meaning a) result = Some (all p) -> safe a (result :: proofs).
Proof.
  intros Hsafe Hin Hp Hresult j [<- | Hj]; [|now apply Hsafe].
  exists (all p). split; [exact Hresult |].
  destruct (Hsafe source Hin) as [q [Hq Hd]]. rewrite Hp in Hq. injection Hq as <-.
  now apply d_gen.
Qed.

(* These forms use the same ID comparisons as the imperative proof commands.
   The meaning of each child comes from the arena invariant, rather than from
   a caller-supplied claim about the implication's antecedent/consequent. *)
Theorem modus_ponens_on_ids a proofs implication antecedent result :
  represents a -> safe a proofs -> In implication proofs -> In antecedent proofs ->
  nth_error (nodes a) implication = Some (imp_node antecedent result) ->
  safe a (result :: proofs).
Proof.
  intros Hrep Hsafe Hi Ha Hnode.
  destruct (represented_lookup _ _ _ Hrep Hnode) as [p [Hp Hdecode]].
  cbn [decode_node] in Hdecode.
  destruct (nth_error (meaning a) antecedent) as [left |] eqn:Hleft; [|discriminate].
  destruct (nth_error (meaning a) result) as [right |] eqn:Hright; [|discriminate].
  injection Hdecode as <-.
  exact (modus_ponens_sound a proofs implication antecedent result left right
    Hsafe Hi Ha Hp Hleft Hright).
Qed.

Theorem generalize_on_ids a proofs source result :
  represents a -> safe a proofs -> In source proofs ->
  nth_error (nodes a) result = Some (all_node source) -> safe a (result :: proofs).
Proof.
  intros Hrep Hsafe Hin Hnode.
  destruct (represented_lookup _ _ _ Hrep Hnode) as [q [Hq Hdecode]].
  cbn [decode_node] in Hdecode.
  destruct (nth_error (meaning a) source) as [p |] eqn:Hp; [|discriminate].
  injection Hdecode as <-.
  exact (generalize_sound a proofs source result p Hsafe Hin Hp Hq).
Qed.

Theorem no_false_if_consistent a proofs : SetTheory.consistent -> safe a proofs ->
  forall i, In i proofs -> nth_error (meaning a) i <> Some falsity.
Proof.
  intros Hcon Hsafe i Hin Hfalse. destruct (Hsafe i Hin) as [p [Hp Hd]].
  rewrite Hfalse in Hp. injection Hp as <-. exact (Hcon Hd).
Qed.
End Arena.
