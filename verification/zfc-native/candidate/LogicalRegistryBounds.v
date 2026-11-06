From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import numbers list.

Module LogicalRegistryBounds.
Definition unique (s:Protocol.state) := NoDup(map fst (Protocol.bindings s)).
Lemma absent_key bindings name : Protocol.lookup name bindings=None -> ~In name (map fst bindings).
Proof.
 induction bindings as [|[key meaning] bindings IH];[cbn;tauto|].
 cbn [Protocol.lookup map fst]. destruct(Protocol.name_eq_dec name key) as [->|Hdifferent];[discriminate|].
 intros Habsent [Hequal|Hin];[congruence|exact(IH Habsent Hin)].
Qed.
Lemma append_key bindings name meaning : NoDup(map fst bindings) -> Protocol.lookup name bindings=None ->
 NoDup(map fst (bindings++[(name,meaning)])).
Proof.
 intros Hunique Habsent. rewrite map_app. apply NoDup_app. split;[exact Hunique|]. split.
 - intros key Hin Hsingleton. cbn [map fst] in Hsingleton. apply list_elem_of_In in Hsingleton.
   destruct Hsingleton as [Hequal|Hfalse];[|contradiction]. subst key.
   apply(absent_key bindings name Habsent). now apply list_elem_of_In.
 - constructor;[apply not_elem_of_nil|constructor].
Qed.
Lemma marked_keys bindings name cls :
 map fst (map (fun item=>if Protocol.name_eq_dec name (fst item) then (name,Protocol.class_binding cls true) else item) bindings)=map fst bindings.
Proof.
 induction bindings as [|[key meaning] bindings IH];[reflexivity|].
 cbn [map fst]. destruct(Protocol.name_eq_dec name key) as [->|Hdifferent];cbn [fst];now rewrite IH.
Qed.
Theorem accepted_unique source request reply after :
 Protocol.accepted source request reply after -> unique source -> unique after.
Proof.
 intros Haccepted Hunique. destruct Haccepted;unfold unique in *;cbn [Protocol.bindings Protocol.with_history] in *;
 try exact Hunique;try (apply append_key;assumption).
 now rewrite marked_keys.
Qed.
Theorem step_unique source request reply after :
 Protocol.step source request reply after -> unique source -> unique after.
Proof.
 intros Hstep Hunique. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hprefix [Hdistinct [Hclasses [Hhistory [Hbindings Hexpressions]]]]];
 unfold unique;rewrite Hbindings;[exact(accepted_unique _ _ _ _ Haccepted Hunique)|exact Hunique].
Qed.
Theorem dialogue_unique source requests replies after remaining :
 Protocol.dialogue source requests replies after remaining -> unique source -> unique after.
Proof.
 intro Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH];[trivial|trivial|]. intro Hunique. apply IH.
 eapply step_unique;eassumption.
Qed.
Lemma initial_unique : unique Protocol.initial.
Proof. constructor. Qed.
Theorem initial_dialogue_unique requests replies after remaining :
 Protocol.dialogue Protocol.initial requests replies after remaining -> unique after.
Proof. intro Hdialogue. exact(dialogue_unique _ _ _ _ _ Hdialogue initial_unique). Qed.

Definition counts source after allowance :=
 (length (Protocol.bindings after)<=length (Protocol.bindings source)+allowance)%nat /\
 (length (Protocol.history after)<=length (Protocol.history source)+allowance)%nat /\
 (length (Protocol.expressions after)<=length (Protocol.expressions source)+allowance)%nat.
Theorem accepted_counts source request reply after :
 Protocol.accepted source request reply after -> counts source after 1.
Proof.
 intro Haccepted. destruct Haccepted;unfold counts;
 cbn [Protocol.bindings Protocol.history Protocol.expressions Protocol.with_history];
 rewrite ?app_length,?map_length;cbn [length];repeat split;try lia.
 match goal with H:Protocol.history _=_++[_] |- _=>rewrite H,app_length;cbn [length];lia end.
Qed.
Theorem step_counts source request reply after :
 Protocol.step source request reply after -> counts source after 1.
Proof.
 intro Hstep. destruct Hstep as [reply middle after Haccepted Hretained|after Hnone Hretained];
 destruct Hretained as [Hprefix [Hdistinct [Hclasses [Hhistory [Hbindings Hexpressions]]]]];
 unfold counts;rewrite Hbindings,Hhistory,Hexpressions.
 - exact(accepted_counts _ _ _ _ Haccepted).
 - repeat split;lia.
Qed.
Lemma counts_trans source middle after first second : counts source middle first -> counts middle after second ->
 counts source after (first+second).
Proof. unfold counts;intros [Hbindings [Hhistory Hexpressions]] [Hbindings' [Hhistory' Hexpressions']];repeat split;lia. Qed.
Theorem dialogue_counts source requests replies after remaining :
 Protocol.dialogue source requests replies after remaining -> counts source after (length requests).
Proof.
 intro Hdialogue. induction Hdialogue as [s|s tail|s q tail r t rs final remaining Hop Hstep Hdialogue IH].
 - unfold counts;repeat split;lia.
 - unfold counts;cbn [length];repeat split;lia.
 - change(counts s final (1+length tail)). eapply counts_trans;[eapply step_counts;exact Hstep|exact IH].
Qed.
End LogicalRegistryBounds.
