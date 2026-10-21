From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash NameSearch NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module TypedNameLookup.
Import IndexExecution SipHashExecution NameSearchExecution.
Definition binding_kind meaning := match meaning with
| Protocol.class_binding _ _ => 0 | Protocol.theorem_binding _ => 1 | Protocol.schema_binding _ => 2 end.
Definition binding_value meaning := match meaning with
| Protocol.class_binding id _ | Protocol.theorem_binding id | Protocol.schema_binding id => id end.
Lemma decode_kind value flag kind meaning : NameRepresentation.decode value flag kind = Some meaning -> kind = binding_kind meaning.
Proof.
  unfold NameRepresentation.decode. destruct (Z.eq_dec kind 0) as [->|H0]; [|destruct (Z.eq_dec kind 1) as [->|H1]; [|destruct (Z.eq_dec kind 2) as [->|H2]]];
    intro H; inversion H; reflexivity.
Qed.
Lemma decode_value value flag kind meaning : word value -> NameRepresentation.decode value flag kind = Some meaning ->
  value = Z.of_nat (binding_value meaning).
Proof.
  intros Hword. unfold NameRepresentation.decode.
  destruct (Z.eq_dec kind 0) as [->|H0]; [|destruct (Z.eq_dec kind 1) as [->|H1]; [|destruct (Z.eq_dec kind 2) as [->|H2]]];
    intro H; inversion H; cbn [binding_value]; now rewrite Z2Nat.id by exact (proj1 Hword).
Qed.
Lemma decode_flag value flag kind id certified : (flag = 0 \/ flag = 1) ->
  NameRepresentation.decode value flag kind = Some (Protocol.class_binding id certified) ->
  flag = if certified then 1 else 0.
Proof.
  intros Hflag Hdecode. pose proof (decode_kind value flag kind _ Hdecode) as Hkind.
  change (kind = 0) in Hkind. subst kind. unfold NameRepresentation.decode in Hdecode. cbn in Hdecode.
  injection Hdecode as Hid Hcert. destruct Hflag as [Hflag|Hflag]; subst flag.
  - change (false = certified) in Hcert. subst certified. reflexivity.
  - change (true = certified) in Hcert. subst certified. reflexivity.
Qed.
Definition outcome s bindings name := match Protocol.lookup name bindings with
| None => meta_value s 0 = maximum
| Some meaning => exists index raw, meta_value s 0 = Z.of_nat index /\
    0 <= Z.of_nat index < maximum /\ (index < length (memory s arraydef_0__bindings))%nat /\
    List.nth index (memory s arraydef_0__bindings) (0,0,0,0,0) = raw /\
    NameRepresentation.entry_rep (memory s arraydef_0__names) raw (name,meaning)
end.
Theorem generated s bs ns bindings name observations :
  (6 < length (memory s arraydef_0__meta))%nat -> NameRepresentation.represents s bindings -> NameRepresentation.token_rep s name ->
  exists final, execObserved (funcdef_0__lookup bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NameRepresentation.represents final bindings /\
    length (memory final arraydef_0__meta) = length (memory s arraydef_0__meta) /\
    storage_frame s final /\ outcome final bindings name.
Proof.
  intros Hmeta Hrep Htoken.
  destruct (generated_lookup_with_capacity s bs ns (length bindings) (length name) observations Hmeta
    (proj1 Hrep) (proj1 Htoken) (proj1 (proj2 Htoken)) (NameRepresentation.valid_storage s bindings Hrep))
    as [final [Hrun [Hcorrect Hlength]]].
  destruct Hcorrect as [Hresult Hframe].
  pose proof (NameRepresentation.storage_transport s final bindings Hframe Hrep) as Hrep'.
  exists final. split; [exact Hrun|]. split; [exact Hrep'|]. split; [exact Hlength|]. split; [exact Hframe|].
  pose proof (NameRepresentation.lookup_correspondence s bindings name Hrep Htoken) as Hlogical.
  unfold outcome. destruct (find_native s (length bindings) (length name) (length bindings)) as [index|] eqn:Hfind.
  - destruct Hlogical as [meaning [Hentry Hlookup]]. rewrite Hlookup.
    destruct (NameRepresentation.represented_lookup final bindings index (name,meaning) Hrep' Hentry) as [raw [Hraw Hmeaning]].
    exists index,raw. split; [exact Hresult|]. split.
    + exact (found_below_sentinel s (length bindings) (length name) index (proj1 (proj2 (proj2 Hrep))) Hfind).
    + split; [apply nth_error_Some; congruence|]. split.
      * exact (List.nth_error_nth _ _ (0,0,0,0,0) Hraw).
      * exact Hmeaning.
  - rewrite Hlogical. exact Hresult.
Qed.
End TypedNameLookup.
