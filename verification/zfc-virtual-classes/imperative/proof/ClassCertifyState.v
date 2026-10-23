From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NameSearch NameRepresentation ReadName NameQueryState DecimalInput
  ArenaFrame FormulaProjection SemanticFrames ClassStorage HistoryRefinement SchemaMetadata ClassLookup RenameMemoParseDomain RenameMemoClassSetness
  ClassCertifyCommand ReplyOK ReplyNO InternTail Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassCertifyState.
Import IndexExecution SipHashExecution NameSearchExecution.
Definition frame (s t : Machine) :=
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  (forall name,name<>arraydef_0__meta -> name<>arraydef_0__token -> memory t name=memory s name) /\
  (forall i,i<>0%nat -> i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat -> i<>17%nat ->
    meta_value t i=meta_value s i).
Lemma frame_trans s t u : frame s t -> frame t u -> frame s u.
Proof.
  intros [Hm [Ha Hc]] [Hm' [Ha' Hc']]. split; [congruence|]. split.
  - intros name H1 H2. now rewrite Ha',Ha by assumption.
  - intros i H0 H6 H11 H14 H15 H17. now rewrite Hc',Hc by assumption.
Qed.
Lemma named_frame s ch chars name sep tail : (17<length (memory s arraydef_0__meta))%nat ->
  frame s (ReadName.name_state s ch chars name sep tail).
Proof.
  intro Hmeta. split; [apply ReadName.name_meta_length|]. split; [now apply ReadName.name_other|].
  intros i H0 H6 H11 H14 H15 H17. now apply ReadName.name_meta_other.
Qed.
Lemma looked_frame s t : storage_frame s t ->
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) -> frame s t.
Proof. intros [Ha [Hc Hio]] Hm. split; [exact Hm|]. split; [intros; now apply Ha|]. intros; apply Hc; assumption. Qed.
Lemma number_frame s value tail : (17<length (memory s arraydef_0__meta))%nat ->
  frame s (DecimalInput.encoded_result s value tail).
Proof.
  intro Hm. split; [apply DecimalInput.encoded_meta_length|]. split; [now apply DecimalInput.encoded_other|].
  intros i H0 H6 H11 H14 H15 H17. now apply DecimalInput.encoded_meta_other.
Qed.
Lemma arena_frame s t : frame s t -> ArenaFrame.storage s t.
Proof.
  intros [Hm [Ha Hc]]. split; [exact Hm|]. split; [exact Ha|]. repeat split; apply Hc; lia.
Qed.
Lemma classes s t fs cs : frame s t -> ClassStorage.represents s fs cs -> ClassStorage.represents t fs cs.
Proof. intros [Hm [Ha Hc]] [Hcount Hentries]. split; [rewrite Hc by lia; exact Hcount|]. now rewrite Ha by discriminate. Qed.
Lemma history s t logical : frame s t -> HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof. intros [Hm [Ha Hc]] [Hcount Hentries]. split; [rewrite Hc by lia; exact Hcount|]. now rewrite Ha by discriminate. Qed.
Lemma names s t bindings : frame s t -> NameRepresentation.represents s bindings -> NameRepresentation.represents t bindings.
Proof.
  intros [Hm [Ha Hc]] [Hcount [Hbytes [Hlimit [Hspan Hentries]]]]. unfold NameRepresentation.represents.
  rewrite (Ha arraydef_0__names ltac:(discriminate) ltac:(discriminate)),
    (Ha arraydef_0__bindings ltac:(discriminate) ltac:(discriminate)).
  rewrite !Hc by lia. repeat split; assumption.
Qed.
Lemma schemas s t expressions : frame s t -> SchemaMetadata.represents s expressions -> SchemaMetadata.represents t expressions.
Proof. intros [Hm [Ha Hc]]. apply SchemaMetadata.transport; [apply Hc; lia|apply Ha; discriminate]. Qed.
Lemma ready s t fs index cls : frame s t -> RenameMemoClassSetness.ready s fs index cls -> RenameMemoClassSetness.ready t fs index cls.
Proof.
  intros Hframe. destruct cls; cbn [RenameMemoClassSetness.ready]; [exact (fun H=>H)|].
  apply RenameMemoParseDomain.predicate_ready. now apply arena_frame.
Qed.
Lemma work s t index cls : frame s t -> RenameMemoClassSetness.work t index cls=RenameMemoClassSetness.work s index cls.
Proof.
  intro Hframe. destruct cls; cbn [RenameMemoClassSetness.work]; [reflexivity|].
  now rewrite (RenameMemoParseDomain.growth_same s t index (arena_frame s t Hframe)).
Qed.
Theorem lookup_present s bs ns bindings name meaning observations :
  (6<length (memory s arraydef_0__meta))%nat -> NameRepresentation.represents s bindings ->
  NameRepresentation.token_rep s name -> Protocol.lookup name bindings=Some meaning ->
  exists final index raw,
    execObserved (funcdef_0__lookup bs ns) (s,observations)=Some (tt,(final,observations)) /\
    frame s final /\ storage_frame s final /\ stdin final=stdin s /\ stdout final=stdout s /\
    meta_value final 0=Z.of_nat index /\ 0<=Z.of_nat index<maximum /\
    nth_error bindings index=Some (name,meaning) /\
    nth_error (memory final arraydef_0__bindings) index=Some raw /\
    NameRepresentation.entry_rep (memory final arraydef_0__names) raw (name,meaning).
Proof.
  intros Hmeta Hrep Htoken Hlookup.
  destruct (generated_lookup_with_capacity s bs ns (length bindings) (length name) observations Hmeta
    (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [final [Hrun [[Hresult Hstorage] Hlength]]].
  pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hlogical.
  destruct (find_native s (length bindings) (length name) (length bindings)) as [index|] eqn:Hfind;
    [|congruence].
  destruct Hlogical as [other [Hentry Hmeaning]]. assert (other=meaning) by congruence. subst other.
  pose proof (NameRepresentation.storage_transport s final bindings Hstorage Hrep) as Hnext.
  destruct (NameRepresentation.represented_lookup final bindings index _ Hnext Hentry) as [raw [Hraw Hrecord]].
  exists final,index,raw. split; [exact Hrun|]. split; [now apply looked_frame|]. split; [exact Hstorage|].
  destruct Hstorage as [Ha [Hc [Hin Hout]]]. split; [exact Hin|]. split; [exact Hout|].
  split; [exact Hresult|]. split.
  - exact (found_below_sentinel s (length bindings) (length name) index (proj1 (proj2 (proj2 Hrep))) Hfind).
  - repeat split; assumption.
Qed.
Lemma In_member {A : Type} (xs : list A) x : In x xs -> x∈xs.
Proof. induction xs as [|head rest IH]; [contradiction|]. cbn [In]. intros [<-|H]; apply elem_of_cons; [now left|right; now apply IH]. Qed.
Definition mark name cls (item : Protocol.name*Protocol.binding) :=
  if Protocol.name_eq_dec name (fst item) then (name,Protocol.class_binding cls true) else item.
Lemma mark_insert bindings name cls flag index : NoDup (map fst bindings) ->
  nth_error bindings index=Some (name,Protocol.class_binding cls flag) ->
  map (mark name cls) bindings=<[index:=(name,Protocol.class_binding cls true)]>bindings.
Proof.
  induction bindings as [|[key meaning] rest IH] in index |- *; [destruct index; discriminate|].
  intros Hunique Hentry. inversion Hunique as [|k keys Hfresh Hrest]; subst.
  destruct index as [|index].
  - cbn [nth_error] in Hentry. injection Hentry as Hkey Hmeaning. subst key meaning.
    change (mark name cls (name,Protocol.class_binding cls flag)::map (mark name cls) rest=
      (name,Protocol.class_binding cls true)::rest).
    unfold mark at 1. cbn [fst]. destruct (Protocol.name_eq_dec name name); [|congruence]. f_equal.
    transitivity (map (fun item=>item) rest); [|apply map_id].
    apply map_ext_in. intros [other value] Hitem. unfold mark. cbn [fst].
    destruct (Protocol.name_eq_dec name other); [|reflexivity]. subst other. exfalso.
    apply Hfresh. apply in_map with (f:=fst) in Hitem. now apply In_member.
  - cbn [nth_error] in Hentry.
    change (mark name cls (key,meaning)::map (mark name cls) rest=
      (key,meaning)::<[index:=(name,Protocol.class_binding cls true)]>rest).
    unfold mark at 1. cbn [fst]. destruct (Protocol.name_eq_dec name key) as [Heq|Hne].
    + subst key. exfalso. apply Hfresh. pose proof (List.nth_error_In _ _ Hentry) as Hin.
      apply in_map with (f:=fst) in Hin. now apply In_member.
    + f_equal. now apply IH.
Qed.
Lemma certified_names s bindings name cls flag index offset size rawflag :
  NameRepresentation.represents s bindings -> NoDup (map fst bindings) ->
  nth_error bindings index=Some (name,Protocol.class_binding cls flag) ->
  nth_error (memory s arraydef_0__bindings) index=Some (offset,size,Z.of_nat cls,rawflag,0) ->
  NameRepresentation.represents (ClassCertifyCommand.certified s index offset size cls) (map (mark name cls) bindings).
Proof.
  intros [Hcount [Hbytes [Hlimit [Hspan Hentries]]]] Hunique Hentry Hraw.
  rewrite (mark_insert bindings name cls flag index Hunique Hentry).
  unfold NameRepresentation.represents.
  assert (Hm : memory (ClassCertifyCommand.certified s index offset size cls) arraydef_0__meta=memory s arraydef_0__meta)
    by (apply ClassCertifyCommand.certified_other; discriminate).
  assert (Hn : memory (ClassCertifyCommand.certified s index offset size cls) arraydef_0__names=memory s arraydef_0__names)
    by (apply ClassCertifyCommand.certified_other; discriminate).
  unfold meta_value. rewrite Hm,Hn,length_insert. split; [exact Hcount|]. split; [exact Hbytes|].
  split; [exact Hlimit|]. split; [exact Hspan|].
  change (Forall2 (NameRepresentation.entry_rep (memory s arraydef_0__names))
    (<[index:=(offset,size,Z.of_nat cls,1,0)]>(memory s arraydef_0__bindings))
    (<[index:=(name,Protocol.class_binding cls true)]>bindings)).
  apply Forall2_insert; [exact Hentries|].
  assert (Hold : NameRepresentation.entry_rep (memory s arraydef_0__names)
    (offset,size,Z.of_nat cls,rawflag,0) (name,Protocol.class_binding cls flag)).
  { eapply Forall2_lookup_lr with (i:=index); [exact Hentries| |].
    - exact (eq_trans (SemanticFrames.lookup_nth_error (memory s arraydef_0__bindings) index) Hraw).
    - exact (eq_trans (SemanticFrames.lookup_nth_error bindings index) Hentry). }
  destruct Hold as [Hsize [Hoffset [Hoffsetword [Hvalue [Hflag [Hbytesbound [Hcontent [Hdecode Hvalid]]]]]]]].
  unfold NameRepresentation.entry_rep. split; [exact Hsize|]. split; [exact Hoffset|].
  split; [exact Hoffsetword|]. split; [exact Hvalue|]. split; [now right|].
  split; [exact Hbytesbound|]. split; [exact Hcontent|]. split; [|exact Hvalid].
  unfold NameRepresentation.decode. cbn. now rewrite Nat2Z.id.
Qed.
Lemma result_other s index offset size cls matches array : array<>arraydef_0__printBuffer -> array<>arraydef_0__bindings ->
  memory (ClassCertifyCommand.result s index offset size cls matches) array=memory s array.
Proof.
  intros Hp Hb. destruct matches; cbn [ClassCertifyCommand.result].
  - rewrite ReplyOKExecution.reply_other by exact Hp. now apply ClassCertifyCommand.certified_other.
  - apply ReplyNOExecution.reply_memory.
Qed.
Lemma result_projection s index offset size cls matches :
  FormulaProjection.storage s (ClassCertifyCommand.result s index offset size cls matches).
Proof.
  split; [now rewrite result_other by discriminate|]. split.
  - intros array Hneeded. apply result_other; unfold FormulaProjection.needed in Hneeded;
      destruct Hneeded as [Heq|[Heq|[Heq|Heq]]]; subst array; discriminate.
  - unfold meta_value. rewrite result_other by discriminate. repeat split; reflexivity.
Qed.
Lemma result_classes s index offset size cls matches fs classes : ClassStorage.represents s fs classes ->
  ClassStorage.represents (ClassCertifyCommand.result s index offset size cls matches) fs classes.
Proof.
  intros [Hcount Hentries]. split; [unfold meta_value; now rewrite result_other by discriminate|].
  now rewrite result_other by discriminate.
Qed.
Lemma result_history s index offset size cls matches logical : HistoryRefinement.represents s logical ->
  HistoryRefinement.represents (ClassCertifyCommand.result s index offset size cls matches) logical.
Proof.
  intros [Hcount Hentries]. split; [unfold meta_value; now rewrite result_other by discriminate|].
  now rewrite result_other by discriminate.
Qed.
Lemma result_schemas s index offset size cls matches expressions : SchemaMetadata.represents s expressions ->
  SchemaMetadata.represents (ClassCertifyCommand.result s index offset size cls matches) expressions.
Proof.
  apply SchemaMetadata.transport; [unfold meta_value; now rewrite result_other by discriminate|].
  now rewrite result_other by discriminate.
Qed.
Lemma result_names s index offset size cls matches bindings name flag rawflag :
  NameRepresentation.represents s bindings -> NoDup (map fst bindings) ->
  nth_error bindings index=Some (name,Protocol.class_binding cls flag) ->
  nth_error (memory s arraydef_0__bindings) index=Some (offset,size,Z.of_nat cls,rawflag,0) ->
  NameRepresentation.represents (ClassCertifyCommand.result s index offset size cls matches)
    (if matches then map (mark name cls) bindings else bindings).
Proof.
  intros Hrep Hunique Hentry Hraw. destruct matches; cbn [ClassCertifyCommand.result].
  - pose proof (certified_names s bindings name cls flag index offset size rawflag Hrep Hunique Hentry Hraw) as Hcert.
    unfold NameRepresentation.represents,meta_value in *. rewrite !ReplyOKExecution.reply_other by discriminate. exact Hcert.
  - unfold NameRepresentation.represents,meta_value in *. now rewrite !ReplyNOExecution.reply_memory.
Qed.
End ClassCertifyState.
