From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NameSearch.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameRepresentation.
Import IndexExecution SipHashExecution NameSearchExecution.
Definition decode value flag kind :=
  if Z.eq_dec kind 0 then Some (Protocol.class_binding (Z.to_nat value) (bool_decide (flag = 1))) else
  if Z.eq_dec kind 1 then Some (Protocol.theorem_binding (Z.to_nat value)) else
  if Z.eq_dec kind 2 then Some (Protocol.schema_binding (Z.to_nat value)) else None.
Definition entry_rep bytes (raw : Z*Z*Z*Z*Z) (item : Protocol.name * Protocol.binding) :=
  let '(offset,size,value,flag,kind) := raw in let '(name,meaning) := item in
  size = Z.of_nat (length name) /\ 0 <= offset /\ word (offset + size) /\ word value /\
  (flag = 0 \/ flag = 1) /\ (Z.to_nat offset + length name <= length bytes)%nat /\
  (forall j, (j < length name)%nat -> List.nth (Z.to_nat offset + j) bytes 0 = List.nth j name 0) /\
  decode value flag kind = Some meaning /\ Protocol.valid_name name.
Definition represents s bindings :=
  meta_value s 4 = Z.of_nat (length bindings) /\ meta_value s 5 = Z.of_nat (length (memory s arraydef_0__names)) /\
  Z.of_nat (length bindings) <= maximum /\ Z.of_nat (length (memory s arraydef_0__names)) <= maximum /\
  Forall2 (entry_rep (memory s arraydef_0__names)) (memory s arraydef_0__bindings) bindings.
Lemma related_lookup {A B} (R : A -> B -> Prop) xs ys i y : Forall2 R xs ys -> nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  intros Hrel. induction Hrel as [|x head xs ys Hhead Hrel IH] in i |- *.
  - destruct i; discriminate.
  - destruct i as [|i]; cbn [nth_error].
    + intro H. injection H as <-. exists x. split; [reflexivity|exact Hhead].
    + intro H. destruct (IH i H) as [entry [Hentry Hrep]]. exists entry. split; assumption.
Qed.
Lemma represented_lookup s bindings i item : represents s bindings -> nth_error bindings i = Some item ->
  exists raw, nth_error (memory s arraydef_0__bindings) i = Some raw /\ entry_rep (memory s arraydef_0__names) raw item.
Proof. intros [_ [_ [_ [_ Hrep]]]] Hentry. exact (related_lookup _ _ _ i item Hrep Hentry). Qed.
Lemma represents_length s bindings : represents s bindings -> length (memory s arraydef_0__bindings) = length bindings.
Proof. intros [_ [_ [_ [_ Hrep]]]]. now apply Forall2_length in Hrep. Qed.
Theorem valid_storage s bindings : represents s bindings -> valid_entries s (length bindings).
Proof.
  intro Hrep. split; [rewrite (represents_length s bindings Hrep); lia|]. intros i Hi.
  destruct (nth_error bindings i) as [item|] eqn:Hitem; [|apply nth_error_None in Hitem; lia].
  destruct (represented_lookup s bindings i item Hrep Hitem) as [raw [Hraw Hentry]].
  destruct raw as [[[[offset size] value] flag] kind],item as [name meaning].
  destruct Hentry as [Hsize [Hoffset [Hword [_ [_ [Hspan _]]]]]].
  exists offset,(length name),value,flag,kind. split.
  - unfold binding_at. rewrite <-Hsize. exact (List.nth_error_nth _ _ (0,0,0,0,0) Hraw).
  - split; [exact Hoffset|]. split; [now rewrite <-Hsize|exact Hspan].
Qed.
Theorem storage_transport s t bindings : storage_frame s t -> represents s bindings -> represents t bindings.
Proof.
  intros [Harrays [Hcells _]] [Hcount [Hbytes [Hbindinglimit [Hlimit Hrep]]]]. split.
  - rewrite Hcells by lia. exact Hcount.
  - rewrite (Harrays arraydef_0__names ltac:(discriminate)). split; [now rewrite Hcells by lia|].
    split; [exact Hbindinglimit|]. split; [exact Hlimit|]. now rewrite (Harrays arraydef_0__bindings ltac:(discriminate)).
Qed.
Definition token_rep s name := meta_value s 6 = Z.of_nat (length name) /\
  (length name <= length (memory s arraydef_0__token))%nat /\
  forall j, (j < length name)%nat -> List.nth j (memory s arraydef_0__token) 0 = List.nth j name 0.
Theorem lookup_preserves_names s bs ns bindings name observations :
  (6 < length (memory s arraydef_0__meta))%nat -> represents s bindings -> token_rep s name ->
  exists final, execObserved (funcdef_0__lookup bs ns) (s,observations) = Some (tt,(final,observations)) /\
    lookup_correct s final (find_native s (length bindings) (length name) (length bindings)) /\ represents final bindings.
Proof.
  intros Hmeta Hrep [Hsize [Htoken Hbytes]].
  destruct (generated_lookup s bs ns (length bindings) (length name) observations Hmeta (proj1 Hrep) Hsize Htoken (valid_storage s bindings Hrep))
    as [final [Hrun Hlookup]]. exists final. split; [exact Hrun|]. split; [exact Hlookup|].
  exact (storage_transport s final bindings (proj2 Hlookup) Hrep).
Qed.
Lemma entry_matches_key s raw key meaning name i : entry_rep (memory s arraydef_0__names) raw (key,meaning) ->
  token_rep s name -> binding_at s i = raw -> (entry_matches s (length name) i <-> key = name).
Proof.
  destruct raw as [[[[offset size] value] flag] kind].
  intros [Hsize [Hoffset [Hword [Hvalue [Hflag [Hspan [Hbytes [Hdecode Hvalid]]]]]]]]
    [Htokenlen [Htokenbound Htoken]] Hraw.
  unfold entry_matches. rewrite Hraw. split.
  - intros [Hlength Hsame]. assert (Hlen : length key = length name) by lia.
    apply List.nth_ext with (d := 0%Z) (d' := 0%Z); [exact Hlen|]. intros j Hj.
    rewrite <-(Hbytes j Hj), <-(Htoken j ltac:(lia)). apply Hsame. lia.
  - intro Heq. subst key. split; [exact Hsize|]. intros j Hj. rewrite Hbytes,Htoken by exact Hj. reflexivity.
Qed.
Theorem key_at s bindings name i key meaning : represents s bindings -> token_rep s name ->
  nth_error bindings i = Some (key,meaning) -> (entry_matches s (length name) i <-> key = name).
Proof.
  intros Hrep Htoken Hitem. destruct (represented_lookup s bindings i _ Hrep Hitem) as [raw [Hraw Hentry]].
  apply (entry_matches_key s raw key meaning name i Hentry Htoken).
  unfold binding_at. exact (List.nth_error_nth _ _ (0,0,0,0,0) Hraw).
Qed.
Lemma lookup_first bindings name index meaning : nth_error bindings index = Some (name,meaning) ->
  (forall j key value, (j < index)%nat -> nth_error bindings j = Some (key,value) -> key <> name) ->
  Protocol.lookup name bindings = Some meaning.
Proof.
  induction index as [|index IH] in bindings |- *; destruct bindings as [|[key value] bindings]; try discriminate.
  - intros Hentry _. cbn [nth_error] in Hentry. injection Hentry as Hkey Hmeaning. subst key value.
    cbn [Protocol.lookup]. destruct (Protocol.name_eq_dec name name); [reflexivity|congruence].
  - intros Hentry Hfirst. cbn [Protocol.lookup]. destruct (Protocol.name_eq_dec name key) as [Heq|Hne].
    + exfalso. apply (Hfirst 0%nat key value ltac:(lia) eq_refl). congruence.
    + apply IH; [exact Hentry|]. intros j k v Hj Hlookup. apply (Hfirst (S j) k v); [lia|exact Hlookup].
Qed.
Lemma lookup_absent bindings name :
  (forall i meaning, nth_error bindings i <> Some (name,meaning)) -> Protocol.lookup name bindings = None.
Proof.
  induction bindings as [|[key value] bindings IH]; intro Habsent; [reflexivity|].
  cbn [Protocol.lookup]. destruct (Protocol.name_eq_dec name key) as [Heq|Hne].
  - subst key. exfalso. exact (Habsent 0%nat value eq_refl).
  - apply IH. intros i meaning Hentry. exact (Habsent (S i) meaning Hentry).
Qed.
Theorem lookup_correspondence s bindings name : represents s bindings -> token_rep s name ->
  match find_native s (length bindings) (length name) (length bindings) with
  | Some index => exists meaning, nth_error bindings index = Some (name,meaning) /\ Protocol.lookup name bindings = Some meaning
  | None => Protocol.lookup name bindings = None end.
Proof.
  intros Hrep Htoken. destruct (find_native s (length bindings) (length name) (length bindings)) as [index|] eqn:Hfind.
  - destruct (find_some s (length bindings) (length name) (length bindings) index ltac:(lia) Hfind) as [Hrange [Hmatch Hfirst]].
    destruct (nth_error bindings index) as [[key meaning]|] eqn:Hentry; [|apply nth_error_None in Hentry; lia].
    apply (proj1 (key_at s bindings name index key meaning Hrep Htoken Hentry)) in Hmatch. subst key.
    exists meaning. split; [reflexivity|]. apply (lookup_first bindings name index meaning Hentry).
    intros j key value Hj Hlookup Heq. subst key.
    apply (Hfirst j ltac:(lia)). apply (proj2 (key_at s bindings name j name value Hrep Htoken Hlookup)). reflexivity.
  - pose proof (proj1 (find_none s (length bindings) (length name) (length bindings) ltac:(lia)) Hfind) as Hnone.
    apply lookup_absent. intros i meaning Hentry.
    assert (Hi : (i < length bindings)%nat) by (apply nth_error_Some; congruence).
    apply (Hnone i ltac:(lia)). apply (proj2 (key_at s bindings name i name meaning Hrep Htoken Hentry)). reflexivity.
Qed.
Theorem generated_dictionary_lookup s bs ns bindings name observations :
  (6 < length (memory s arraydef_0__meta))%nat -> represents s bindings -> token_rep s name ->
  exists final result, execObserved (funcdef_0__lookup bs ns) (s,observations) = Some (tt,(final,observations)) /\
    lookup_correct s final result /\ represents final bindings /\
    match result with
    | Some index => exists meaning, nth_error bindings index = Some (name,meaning) /\
        Protocol.lookup name bindings = Some meaning /\ 0 <= Z.of_nat index < maximum
    | None => Protocol.lookup name bindings = None end.
Proof.
  intros Hmeta Hrep Htoken. destruct (lookup_preserves_names s bs ns bindings name observations Hmeta Hrep Htoken)
    as [final [Hrun [Hcorrect Hnext]]].
  exists final,(find_native s (length bindings) (length name) (length bindings)).
  split; [exact Hrun|]. split; [exact Hcorrect|]. split; [exact Hnext|].
  pose proof (lookup_correspondence s bindings name Hrep Htoken) as Hmeaning.
  destruct (find_native s (length bindings) (length name) (length bindings)) as [index|] eqn:Hfind; [|exact Hmeaning].
  destruct Hmeaning as [meaning [Hentry Hlookup]]. exists meaning. split; [exact Hentry|]. split; [exact Hlookup|].
  exact (found_below_sentinel s (length bindings) (length name) index (proj1 (proj2 (proj2 Hrep))) Hfind).
Qed.
End NameRepresentation.
