From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoBounds.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

(* A cost model of the four-phase depth-first scheduler. This is not an
   execution refinement: native cache contents, frame phases and counters
   must still be connected to this model. Entries are installed on return,
   after all children, exactly as in the imperative implementation. *)
Module RenameMemoWork.
Inductive shape := leaf | binary (left right : nat) | binder (body : nat).
Definition key := (nat*nat)%type.
Definition older (graph : nat->shape) := forall node,
  match graph node with leaf=>True | binary lhs rhs=>lhs<node /\ rhs<node | binder body=>body<node end.
Definition key_eq_dec : forall a b:key, {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Fixpoint run fuel (graph : nat->shape) node depth (seen : list key) : option (list key*nat) :=
  match fuel with
  | 0=>None
  | S rest=>if in_dec key_eq_dec (node,depth) seen then Some (seen,1)
    else match graph node with
    | leaf=>Some ((node,depth)::seen,1)
    | binary lhs rhs=>
      match run rest graph lhs depth seen with
      | None=>None
      | Some (after_left,left_steps)=>
        match run rest graph rhs depth after_left with
        | None=>None
        | Some (after_right,right_steps)=>Some ((node,depth)::after_right,left_steps+right_steps+3)
        end
      end
    | binder body=>
      match run rest graph body (S depth) seen with
      | None=>None
      | Some (after_body,body_steps)=>Some ((node,depth)::after_body,body_steps+2)
      end
    end
  end.
Definition bounded node depth (query : key) := depth<=snd query /\ fst query+(snd query-depth)<=node.
Lemma bounded_root node depth : bounded node depth (node,depth).
Proof. unfold bounded; cbn; lia. Qed.
Lemma bounded_child parent depth child query : child<parent -> bounded child depth query -> bounded parent depth query.
Proof. unfold bounded. lia. Qed.
Lemma bounded_binder parent depth child query : child<parent -> bounded child (S depth) query -> bounded parent depth query.
Proof. unfold bounded. lia. Qed.
Lemma root_absent node depth seen added child child_depth :
  ~In (node,depth) seen -> child<node -> Forall (bounded child child_depth) added -> ~In (node,depth) (added++seen).
Proof.
  intros Habsent Hchild Hbound Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [|contradiction].
  apply Forall_forall with (x:=(node,depth)) in Hbound; [|exact Hin]. unfold bounded in Hbound. cbn in Hbound. lia.
Qed.
Theorem run_spec fuel graph node depth seen : older graph -> node<fuel -> NoDup seen ->
  exists final steps added,
    run fuel graph node depth seen=Some (final,steps) /\ final=added++seen /\ NoDup final /\
    Forall (bounded node depth) added /\ In (node,depth) final /\ steps<=4*length added+1.
Proof.
  induction fuel as [|fuel IH] in node,depth,seen |- *; [lia|].
  intros Hgraph Hfuel Hseen. cbn [run]. destruct (in_dec key_eq_dec (node,depth) seen) as [Hhit|Hmiss].
  - exists seen,1,[]. repeat split; try assumption; try constructor; cbn; lia.
  - specialize (Hgraph node) as Hchildren. destruct (graph node) as [|lhs rhs|body] eqn:Hshape.
    + exists ((node,depth)::seen),1,[(node,depth)]. split; [reflexivity|]. split; [reflexivity|].
      split; [now constructor|]. split; [constructor; [apply bounded_root|constructor]|]. split; [now left|cbn; lia].
    + destruct Hchildren as [Hleft Hright].
      destruct (IH lhs depth seen Hgraph ltac:(lia) Hseen)
        as [after_left [left_steps [left_added [Hrunleft [Hleftshape [Hleftdistinct [Hleftbound [Hleftroot Hleftsteps]]]]]]]].
      destruct (IH rhs depth after_left Hgraph ltac:(lia) Hleftdistinct)
        as [after_right [right_steps [right_added [Hrunright [Hrightshape [Hrightdistinct [Hrightbound [Hrightroot Hrightsteps]]]]]]]].
      assert (Hleftabsent : ~In (node,depth) after_left).
      { rewrite Hleftshape. now apply root_absent with (child:=lhs) (child_depth:=depth). }
      assert (Hrightabsent : ~In (node,depth) after_right).
      { rewrite Hrightshape. now apply root_absent with (child:=rhs) (child_depth:=depth). }
      exists ((node,depth)::after_right),(left_steps+right_steps+3),((node,depth)::right_added++left_added).
      rewrite Hrunleft,Hrunright. split; [reflexivity|]. split.
      * rewrite Hrightshape,Hleftshape. now rewrite app_assoc.
      * split; [now constructor|]. split.
        -- constructor; [apply bounded_root|]. apply Forall_app. split.
           ++ eapply Forall_impl; [|exact Hrightbound]. intros query Hbound. now apply bounded_child with (child:=rhs).
           ++ eapply Forall_impl; [|exact Hleftbound]. intros query Hbound. now apply bounded_child with (child:=lhs).
        -- split; [now left|]. cbn [length]. rewrite length_app. lia.
    + destruct (IH body (S depth) seen Hgraph ltac:(lia) Hseen)
        as [after_body [body_steps [body_added [Hrunbody [Hbodyshape [Hbodydistinct [Hbodybound [Hbodyroot Hbodysteps]]]]]]]].
      assert (Hbodyabsent : ~In (node,depth) after_body).
      { rewrite Hbodyshape. now apply root_absent with (child:=body) (child_depth:=S depth). }
      exists ((node,depth)::after_body),(body_steps+2),((node,depth)::body_added).
      rewrite Hrunbody. split; [reflexivity|]. split; [now rewrite Hbodyshape|].
      split; [now constructor|]. split.
      * constructor; [apply bounded_root|]. eapply Forall_impl; [|exact Hbodybound].
        intros query Hbound. now apply bounded_binder with (child:=body).
      * split; [now left|]. cbn [length]. lia.
Qed.
Theorem root_polynomial graph root base : older graph ->
  exists final steps, run (S root) graph root base []=Some (final,steps) /\ NoDup final /\
    In (root,base) final /\ length final<=(S root*S root) /\ steps<=4*(S root*S root)+1 /\ steps<=RenameMemoBounds.fuel root.
Proof.
  intro Hgraph. destruct (run_spec (S root) graph root base [] Hgraph ltac:(lia) (NoDup_nil _))
    as [final [steps [added [Hrun [Hshape [Hdistinct [Hbound [Hroot Hsteps]]]]]]]].
  rewrite app_nil_r in Hshape. subst added.
  assert (Hgrid : Forall (fun query=>fst query<=root /\ base<=snd query<=base+root) final).
  { eapply Forall_impl; [|exact Hbound]. intros [node depth] Hkey. unfold bounded in Hkey. cbn in *. lia. }
  assert (Hsize : length final<=S root*S root).
  { apply (RenameMemoBounds.distinct_pairs_from base (S root) final Hdistinct).
    eapply Forall_impl; [|exact Hgrid]. intros [node depth] [Hnode Hdepth]. cbn in *. lia. }
  exists final,steps. split; [exact Hrun|]. split; [exact Hdistinct|]. split; [exact Hroot|].
  split; [exact Hsize|]. split; [lia|]. unfold RenameMemoBounds.fuel. nia.
Qed.
End RenameMemoWork.
