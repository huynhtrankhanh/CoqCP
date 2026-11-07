From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses Schemata UniformSchemata Protocol Guarantees.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations SetTheory VirtualClasses.

(* A prospective protocol semantics for uniformly certified schemata.  This
   module is deliberately separate from Protocol until the imperative checker
   and its refinement theorem implement the new semantics. *)
Module UniformProtocol.
Record cached_schema := CachedSchema {
  cached_root : nat;
  cached_certificate : Schemata.proof_template;
  cached_conclusion : UniformSchemata.symbolic;
  cached_valid : UniformSchemata.certify cached_certificate = Some cached_conclusion
}.
Record state := State {
  logical : Protocol.state;
  cache : list (Protocol.name * cached_schema)
}.
Definition initial := State Protocol.initial [].
Fixpoint lookup (name : Protocol.name) (xs : list (Protocol.name * cached_schema)) :=
  match xs with
  | [] => None
  | (key, value) :: rest => if Protocol.name_eq_dec name key then Some value else lookup name rest
  end.

Inductive accepted : state -> Protocol.request -> Protocol.reply -> state -> Prop :=
| legacy s q r t : Protocol.opcode q <> 23%nat -> Protocol.opcode q <> 24%nat ->
    Protocol.accepted (logical s) q r t -> accepted s q r (State t (cache s))
| name_schema s n root cert conclusion (H : UniformSchemata.certify cert = Some conclusion) :
    Protocol.pf (logical s) root = Some cert -> Protocol.lookup n (Protocol.bindings (logical s)) = None ->
    accepted s (Protocol.Req 23 [root] n) (Protocol.OK root)
      (State (Protocol.State (Protocol.formulas (logical s)) (Protocol.classes (logical s))
        (Protocol.history (logical s)) (Protocol.bindings (logical s) ++ [(n,Protocol.schema_binding root)])
        (Protocol.expressions (logical s))) (cache s ++ [(n,CachedSchema root cert conclusion H)]))
| instance s n root entry ids actual p fs cs i :
    Protocol.lookup n (Protocol.bindings (logical s)) = Some (Protocol.schema_binding root) ->
    lookup n (cache s) = Some entry ->
    cached_root entry = root ->
    length ids = Schemata.proof_arity (cached_certificate entry) ->
    Forall2 (fun id c => Protocol.class_at (logical s) id = Some c) ids actual ->
    p = UniformSchemata.evaluate (fun j => List.nth j actual (set 0)) 0 (cached_conclusion entry) ->
    Protocol.allocation (logical s) fs cs i p ->
    accepted s (Protocol.Req 24 ids n) (Protocol.OK (length (Protocol.history (logical s))))
      (State (Protocol.State fs cs (Protocol.history (logical s) ++ [i])
        (Protocol.bindings (logical s)) (Protocol.expressions (logical s))) (cache s)).

Theorem accepted_safe s q r t : accepted s q r t -> Guarantees.safe (logical s) -> Guarantees.safe (logical t).
Proof.
 intros H Hsafe. inversion H; subst; cbn [logical].
 - eapply Guarantees.accepted_safe; eassumption.
 - eapply Guarantees.accepted_safe; [eapply Protocol.accept_name_schema; eassumption|exact Hsafe].
 - eapply Guarantees.append_safe; [exact Hsafe|eassumption|].
   eapply UniformSchemata.certify_sound. apply cached_valid.
Qed.

(* At instantiation only the cached conclusion is evaluated.  Certification is
   evidence produced during naming; no proof-template inference is required. *)
Theorem cached_instance_sound entry rho depth :
  derives (UniformSchemata.evaluate rho depth (cached_conclusion entry)).
Proof. eapply UniformSchemata.certify_sound. apply cached_valid. Qed.

Definition cache_roots s := forall name entry,
  lookup name (cache s) = Some entry ->
  Protocol.pf (logical s) (cached_root entry) = Some (cached_certificate entry).

Lemma lookup_app name xs ys :
  lookup name (xs ++ ys) = match lookup name xs with Some e => Some e | None => lookup name ys end.
Proof.
 induction xs as [|[key value] xs IH]; cbn; [reflexivity|].
 destruct (Protocol.name_eq_dec name key); [reflexivity|exact IH].
Qed.

Lemma pf_extension s t root cert :
  (exists extra, Protocol.expressions t = Protocol.expressions s ++ extra) ->
  Protocol.pf s root = Some cert -> Protocol.pf t root = Some cert.
Proof.
 intros [extra H] Hp. unfold Protocol.pf in *.
 destruct (nth_error (Protocol.expressions s) root) as [e|] eqn:He; [destruct e|]; try discriminate.
 rewrite H, (Guarantees.nth_error_extend _ extra _ _ He). exact Hp.
Qed.

Lemma accepted_expressions s q r t : Protocol.accepted s q r t ->
  exists extra, Protocol.expressions t = Protocol.expressions s ++ extra.
Proof.
 intro H. inversion H; subst; cbn;
   try solve [exists []; now rewrite app_nil_r]; eexists; reflexivity.
Qed.

Lemma binding_lookup_app name xs ys :
  Protocol.lookup name (xs ++ ys) = match Protocol.lookup name xs with
  | Some e => Some e | None => Protocol.lookup name ys end.
Proof.
 induction xs as [|[key value] xs IH]; cbn; [reflexivity|].
 destruct (Protocol.name_eq_dec name key); [reflexivity|exact IH].
Qed.

Lemma certify_preserves_schema name target i flag bs root :
  Protocol.lookup name bs = Some (Protocol.schema_binding root) ->
  Protocol.lookup target bs = Some (Protocol.class_binding i flag) ->
  Protocol.lookup name (map (fun item => if Protocol.name_eq_dec target (fst item)
       then (target,Protocol.class_binding i true) else item) bs) = Some (Protocol.schema_binding root).
Proof.
 intros Hname Htarget.
 assert (Hne : name <> target).
 { intro Heq; subst. congruence. }
 clear Htarget. induction bs as [|[key value] bs IH]; cbn in *; [discriminate|].
 destruct (Protocol.name_eq_dec target key) as [Htarget|Htarget]; cbn.
 - subst key. destruct (Protocol.name_eq_dec name target); [contradiction|].
   destruct (Protocol.name_eq_dec name target); [contradiction|]. now apply IH.
 - destruct (Protocol.name_eq_dec name key); [exact Hname|].
   destruct (Protocol.name_eq_dec name key); [contradiction|]. now apply IH.
Qed.

Lemma accepted_preserves_schema s q r t name root : Protocol.accepted s q r t ->
  Protocol.lookup name (Protocol.bindings s) = Some (Protocol.schema_binding root) ->
  Protocol.lookup name (Protocol.bindings t) = Some (Protocol.schema_binding root).
Proof.
 intros Ha Hl. inversion Ha; subst; cbn in *; try assumption;
   try solve [rewrite binding_lookup_app, Hl; reflexivity].
 eapply certify_preserves_schema; eassumption.
Qed.

Lemma certify_schema_origin name target i bs root :
  Protocol.lookup name (map (fun item => if Protocol.name_eq_dec target (fst item)
       then (target,Protocol.class_binding i true) else item) bs) = Some (Protocol.schema_binding root) ->
  Protocol.lookup name bs = Some (Protocol.schema_binding root).
Proof.
 induction bs as [|[key value] bs IH]; cbn; [discriminate|].
 destruct (Protocol.name_eq_dec target key); cbn.
 - subst key. destruct (Protocol.name_eq_dec name target); [discriminate|].
   destruct (Protocol.name_eq_dec name target); [contradiction|]. apply IH.
 - destruct (Protocol.name_eq_dec name key); [exact (fun H => H)|].
   destruct (Protocol.name_eq_dec name key); [contradiction|]. apply IH.
Qed.

Lemma accepted_schema_origin s q r t name root : Protocol.accepted s q r t ->
  Protocol.opcode q <> 23%nat ->
  Protocol.lookup name (Protocol.bindings t) = Some (Protocol.schema_binding root) ->
  Protocol.lookup name (Protocol.bindings s) = Some (Protocol.schema_binding root).
Proof.
 intros Ha Hne Hl. inversion Ha; subst; cbn in *; try contradiction; try assumption;
   try match type of Hl with context [Protocol.lookup _ (_ ++ _)] =>
     rewrite binding_lookup_app in Hl;
     destruct (Protocol.lookup name (Protocol.bindings s)) as [old|] eqn:Hold;
     [exact Hl|cbn [Protocol.lookup] in Hl;
       repeat match type of Hl with context [if ?dec then _ else _] => destruct dec end; discriminate]
   end.
 eapply certify_schema_origin; eassumption.
Qed.

Theorem accepted_cache_roots s q r t : accepted s q r t -> cache_roots s -> cache_roots t.
Proof.
 intros H Hcache. inversion H; subst; unfold cache_roots in *; cbn [logical cache] in *.
 - intros name entry Hlookup. eapply pf_extension; [eapply accepted_expressions; eassumption|].
   now apply (Hcache name entry).
 - intros name entry Hlookup. rewrite lookup_app in Hlookup.
   destruct (lookup name (cache s)) as [old|] eqn:Hold.
   + inversion Hlookup; subst. now apply (Hcache name entry).
   + cbn [lookup] in Hlookup.
     match type of Hlookup with context [if ?dec then _ else _] => destruct dec end; try discriminate.
     inversion Hlookup; subst. cbn [cached_root cached_certificate]. assumption.
 - exact Hcache.
Qed.

Definition cache_bindings s := forall name entry,
  lookup name (cache s) = Some entry ->
  Protocol.lookup name (Protocol.bindings (logical s)) = Some (Protocol.schema_binding (cached_root entry)).

Theorem accepted_cache_bindings s q r t : accepted s q r t -> cache_bindings s -> cache_bindings t.
Proof.
 intros H Hcache. inversion H; subst; unfold cache_bindings in *; cbn [logical cache] in *.
 - intros name entry Hlookup. eapply accepted_preserves_schema; [eassumption|]. now apply Hcache.
 - intros name entry Hlookup. rewrite lookup_app in Hlookup.
   destruct (lookup name (cache s)) as [old|] eqn:Hold.
   + inversion Hlookup; subst. cbn [Protocol.bindings]. rewrite binding_lookup_app, (Hcache name entry Hold). reflexivity.
   + cbn [lookup] in Hlookup.
     match type of Hlookup with context [if ?dec then _ else _] => destruct dec end; try discriminate.
     inversion Hlookup; subst. cbn [cached_root Protocol.bindings].
     rewrite binding_lookup_app. match goal with Hnone : Protocol.lookup _ _ = None |- _ => rewrite Hnone end.
     cbn [Protocol.lookup]. match goal with |- context [if ?dec then _ else _] => destruct dec end; congruence.
 - exact Hcache.
Qed.

Definition cache_complete s := forall name root,
  Protocol.lookup name (Protocol.bindings (logical s)) = Some (Protocol.schema_binding root) ->
  exists entry, lookup name (cache s) = Some entry /\ cached_root entry = root.

Theorem accepted_cache_complete s q r t : accepted s q r t -> cache_bindings s -> cache_complete s -> cache_complete t.
Proof.
 intros H Hbindings Hcomplete. inversion H; subst; unfold cache_complete, cache_bindings in *; cbn [logical cache] in *.
 - intros name root Hlookup. apply Hcomplete. eapply accepted_schema_origin; eassumption.
 - intros name requested Hlookup. cbn [Protocol.bindings] in Hlookup.
   rewrite binding_lookup_app in Hlookup.
   destruct (Protocol.lookup name (Protocol.bindings (logical s))) as [old|] eqn:Hold.
   + destruct old; try discriminate. inversion Hlookup; subst.
     destruct (Hcomplete name requested Hold) as [entry [Hentry Hroot]].
     exists entry. rewrite lookup_app, Hentry. auto.
   + cbn [Protocol.lookup] in Hlookup.
     match type of Hlookup with context [if ?dec then _ else _] => destruct dec end; try discriminate.
     inversion Hlookup; subst requested.
     assert (Hempty : lookup name (cache s) = None).
     { destruct (lookup name (cache s)) as [entry|] eqn:He; [|reflexivity].
       specialize (Hbindings name entry He). congruence. }
     eexists. rewrite lookup_app, Hempty. cbn [lookup cached_root].
     match goal with |- context [if ?dec then _ else _] => destruct dec end; [split; reflexivity|congruence].
 - exact Hcomplete.
Qed.

Inductive step (s : state) (q : Protocol.request) : Protocol.reply -> state -> Prop :=
| step_accept r t u : accepted s q r t -> Protocol.retained_storage (logical t) u ->
    step s q r (State u (cache t))
| step_reject u : (forall r t, ~ accepted s q r t) -> Protocol.retained_storage (logical s) u ->
    step s q Protocol.NO (State u (cache s)).

Theorem step_safe s q r t : step s q r t -> Guarantees.safe (logical s) -> Guarantees.safe (logical t).
Proof.
 intros H Hsafe. inversion H; subst; cbn [logical].
 - eapply Guarantees.retained; [eassumption|]. eapply accepted_safe; eassumption.
 - eapply Guarantees.retained; eassumption.
Qed.

Theorem step_cache_roots s q r t : step s q r t -> cache_roots s -> cache_roots t.
Proof.
 intros H Hcache. inversion H; subst; unfold cache_roots in *; cbn [logical cache] in *.
 - intros name entry Hlookup. eapply pf_extension.
   + exists []. match goal with Hr : Protocol.retained_storage _ _ |- _ =>
       destruct Hr as [_ [_ [_ [_ [_ Hex]]]]] end. now rewrite Hex, app_nil_r.
   + eapply accepted_cache_roots; eassumption.
 - intros name entry Hlookup. eapply pf_extension.
   + exists []. match goal with Hr : Protocol.retained_storage _ _ |- _ =>
       destruct Hr as [_ [_ [_ [_ [_ Hex]]]]] end. now rewrite Hex, app_nil_r.
   + eapply Hcache; eassumption.
Qed.

Theorem step_cache_bindings s q r t : step s q r t -> cache_bindings s -> cache_bindings t.
Proof.
 intros H Hcache. inversion H; subst; unfold cache_bindings in *; cbn [logical cache] in *.
 - intros name entry Hlookup.
   match goal with Hr : Protocol.retained_storage _ _ |- _ =>
     destruct Hr as [_ [_ [_ [_ [Hb _]]]]] end. rewrite Hb.
   eapply accepted_cache_bindings; eassumption.
 - intros name entry Hlookup.
   match goal with Hr : Protocol.retained_storage _ _ |- _ =>
     destruct Hr as [_ [_ [_ [_ [Hb _]]]]] end. rewrite Hb. now apply Hcache.
Qed.

Theorem step_cache_complete s q r t : step s q r t -> cache_bindings s -> cache_complete s -> cache_complete t.
Proof.
 intros H Hbindings Hcomplete. inversion H; subst; unfold cache_complete in *; cbn [logical cache] in *.
 - intros name root Hlookup.
   match goal with Hr : Protocol.retained_storage _ _ |- _ =>
     destruct Hr as [_ [_ [_ [_ [Hb _]]]]] end. rewrite Hb in Hlookup.
   eapply accepted_cache_complete; eassumption.
 - intros name root Hlookup.
   match goal with Hr : Protocol.retained_storage _ _ |- _ =>
     destruct Hr as [_ [_ [_ [_ [Hb _]]]]] end. rewrite Hb in Hlookup. now apply Hcomplete.
Qed.

Inductive dialogue : state -> list Protocol.request -> list Protocol.reply -> state -> Prop :=
| dialogue_eof s : dialogue s [] [] s
| dialogue_quit s tail : dialogue s (Protocol.Req 0 [] [] :: tail) [Protocol.BYE] s
| dialogue_step s q tail r t rs final : Protocol.opcode q <> 0%nat -> step s q r t ->
    dialogue t tail rs final -> dialogue s (q :: tail) (r :: rs) final.

Theorem dialogue_safe s qs rs t : dialogue s qs rs t -> Guarantees.safe (logical s) -> Guarantees.safe (logical t).
Proof.
 intros H. induction H as [s|s tail|s q tail r t rs final Hnonzero Hstep Hdialogue IH]; intro Hsafe; try exact Hsafe.
 apply IH. eapply step_safe; eassumption.
Qed.

Theorem dialogue_cache_roots s qs rs t : dialogue s qs rs t -> cache_roots s -> cache_roots t.
Proof.
 intros H. induction H as [s|s tail|s q tail r t rs final Hnonzero Hstep Hdialogue IH]; intro Hcache; try exact Hcache.
 apply IH. eapply step_cache_roots; eassumption.
Qed.

Theorem dialogue_cache_bindings s qs rs t : dialogue s qs rs t -> cache_bindings s -> cache_bindings t.
Proof.
 intros H. induction H as [s|s tail|s q tail r t rs final Hnonzero Hstep Hdialogue IH]; intro Hcache; try exact Hcache.
 apply IH. eapply step_cache_bindings; eassumption.
Qed.

Theorem dialogue_cache_complete s qs rs t : dialogue s qs rs t -> cache_bindings s -> cache_complete s -> cache_complete t.
Proof.
 intros H. induction H as [s|s tail|s q tail r t rs final Hnonzero Hstep Hdialogue IH]; intros Hbindings Hcomplete; try exact Hcomplete.
 apply IH; [eapply step_cache_bindings|eapply step_cache_complete]; eassumption.
Qed.

Theorem reachable_named_schema qs rs t name root : dialogue initial qs rs t ->
  Protocol.lookup name (Protocol.bindings (logical t)) = Some (Protocol.schema_binding root) ->
  exists entry, lookup name (cache t) = Some entry /\ cached_root entry = root /\
    Protocol.pf (logical t) root = Some (cached_certificate entry) /\
    UniformSchemata.certify (cached_certificate entry) = Some (cached_conclusion entry).
Proof.
 intros Hdialogue Hlookup.
 assert (Hbindings : cache_bindings initial) by (intros n e H; discriminate).
 assert (Hcomplete : cache_complete initial) by (intros n r H; discriminate).
 destruct (dialogue_cache_complete _ _ _ _ Hdialogue Hbindings Hcomplete name root Hlookup)
   as [entry [Hentry Hroot]]. exists entry. repeat split; try assumption.
 - subst root. eapply (dialogue_cache_roots _ _ _ _ Hdialogue); [|exact Hentry].
   intros n e H. discriminate.
 - apply cached_valid.
Qed.

Theorem reachable_instance_accepted qs rs s name root entry ids actual fs cs i :
  dialogue initial qs rs s ->
  Protocol.lookup name (Protocol.bindings (logical s)) = Some (Protocol.schema_binding root) ->
  lookup name (cache s) = Some entry -> cached_root entry = root ->
  length ids = Schemata.proof_arity (cached_certificate entry) ->
  Forall2 (fun id c => Protocol.class_at (logical s) id = Some c) ids actual ->
  Protocol.allocation (logical s) fs cs i
    (UniformSchemata.evaluate (fun j => List.nth j actual (set 0)) 0 (cached_conclusion entry)) ->
  exists target, accepted s (Protocol.Req 24 ids name) (Protocol.OK (length (Protocol.history (logical s)))) target.
Proof.
 intros _ Hname Hentry Hroot Harity Hargs Halloc. eexists.
 eapply instance; eassumption || reflexivity.
Qed.

Theorem reachable_cache_correspondence qs rs t name entry :
  dialogue initial qs rs t -> lookup name (cache t) = Some entry ->
  Protocol.lookup name (Protocol.bindings (logical t)) = Some (Protocol.schema_binding (cached_root entry)) /\
  Protocol.pf (logical t) (cached_root entry) = Some (cached_certificate entry) /\
  UniformSchemata.certify (cached_certificate entry) = Some (cached_conclusion entry).
Proof.
 intros Hdialogue Hlookup. split.
 - eapply (dialogue_cache_bindings _ _ _ _ Hdialogue); [|exact Hlookup]. intros n e H. discriminate.
 - split; [|apply cached_valid].
 eapply (dialogue_cache_roots _ _ _ _ Hdialogue); [|exact Hlookup].
 intros n e H. discriminate.
Qed.

Theorem initial_dialogue_history_sound qs rs t i p :
  dialogue initial qs rs t -> Protocol.theorem_at (logical t) i = Some p -> derives p.
Proof.
 intros Hdialogue Htheorem. eapply Guarantees.theorem_sound; [|exact Htheorem].
 apply (proj1 (dialogue_safe _ _ _ _ Hdialogue Guarantees.initial_safe)).
Qed.
End UniformProtocol.
