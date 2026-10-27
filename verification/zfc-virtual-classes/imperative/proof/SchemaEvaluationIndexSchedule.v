From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMetadata SchemaRepresentation SchemaMarking
 SchemaMarkingSchedule SchemaMarkingClosure SchemaEvaluationBoundedCell SchemaEvaluationIndexCell
 SchemaEvaluationIndexBudget SchemaEvaluationIndexReady SchemaInstanceGeneralReady.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexSchedule.
Import IndexExecution SipHashExecution.
Record job := Job { job_depth:nat; job_kind:nat; job_a:nat; job_b:nat; job_c:nat; job_d:nat }.
Definition descriptor source root key :=
 let '(k,aa,bb,cc,dd,_,_):=SchemaMetadata.node_at source (key/SchemaGraph.width root) in
 Job (key mod SchemaGraph.width root) (Z.to_nat k) (Z.to_nat aa) (Z.to_nat bb) (Z.to_nat cc) (Z.to_nat dd).
Definition marked source root := SchemaMarkingClosure.sweep (SchemaMarkingSchedule.dependencies source root)
 (SchemaMarkingSchedule.grid (SchemaGraph.width root) (SchemaGraph.width root)) [(root,0%nat)].
Definition active source root (key:nat) :=
 if List.in_dec (fun x y=>decide (x=y)) ((key/SchemaGraph.width root)%nat,(key mod SchemaGraph.width root)%nat) (marked source root)
 then true else false.
Definition advance source root key (state:nat*nat) :=
 if active source root key then
 let task:=descriptor source root key in
 (fst state+SchemaEvaluationIndexBudget.cost (fst state) (job_kind task) (job_a task) (job_depth task),
  SchemaEvaluationIndexCell.successor (job_kind task) (snd state) (job_depth task) (job_b task) (job_c task) (job_d task))%nat
 else state.
Fixpoint state source root initialF initialB count := match count with
 | O=>(initialF,initialB)
 | S key=>advance source root key (state source root initialF initialB key) end.
Definition formula_ceiling source root initialF initialB key := fst (state source root initialF initialB (Nat.min key (SchemaMarking.size root))).
Definition index_ceiling source root initialF initialB key := snd (state source root initialF initialB (Nat.min key (SchemaMarking.size root))).
Definition local_check source root initialF initialB initialC key :=
 if active source root key then
 let task:=descriptor source root key in
 let capacity:=fst (state source root initialF initialB key) in
 (if SchemaEvaluationIndexBudget.renames (job_kind task) (job_a task) (job_depth task) then
   Z.leb (Z.of_nat (5*(capacity*capacity)+1)) maximum else true) &&
 (if SchemaEvaluationIndexBudget.needs_class (job_kind task) (job_depth task) then
   Z.leb (Z.of_nat (initialC+key+1)) maximum else true)
 else true.
(** The only iterations in this check are the finite schema grid and its
    already proved dependency sweep. No successful native run is assumed. *)
Definition check source root initialF initialB initialC :=
 Z.leb (Z.of_nat (fst (state source root initialF initialB (SchemaMarking.size root)))) SchemaEvaluationBoundedCell.bound &&
 Z.leb (Z.of_nat (snd (state source root initialF initialB (SchemaMarking.size root)))) maximum &&
 forallb (local_check source root initialF initialB initialC) (seq 0 (SchemaMarking.size root)).
Lemma key_parts root node dep : (dep<SchemaGraph.width root)%nat ->
 ((SchemaGraph.key root node dep)/SchemaGraph.width root=node /\
  (SchemaGraph.key root node dep) mod SchemaGraph.width root=dep)%nat.
Proof.
 intro Hdepth. split.
 - symmetry. apply (Nat.div_unique (SchemaGraph.key root node dep) (SchemaGraph.width root) node dep);[exact Hdepth|unfold SchemaGraph.key;nia].
 - symmetry. apply (Nat.mod_unique (SchemaGraph.key root node dep) (SchemaGraph.width root) node dep);[exact Hdepth|unfold SchemaGraph.key;nia].
Qed.
Lemma descriptor_key source root node dep kind aa bb cc dd expression :
 (dep<SchemaGraph.width root)%nat ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind aa bb cc dd expression) ->
 descriptor source root (SchemaGraph.key root node dep)=Job dep kind aa bb cc dd.
Proof.
 intros Hdepth Hraw. destruct (key_parts root node dep Hdepth) as [Hnode Hdep].
 unfold descriptor,SchemaMetadata.node_at. rewrite Hnode,Hdep.
 match goal with |- context [@List.nth ?A node ?entries ?zero] =>
  let Hnth:=fresh in assert (Hnth:@List.nth A node entries zero=SchemaRepresentation.encode kind aa bb cc dd expression)
    by exact (List.nth_error_nth _ _ zero Hraw);rewrite Hnth end.
 unfold SchemaRepresentation.encode. now rewrite !Nat2Z.id.
Qed.
Lemma active_key source root node dep : SchemaGraph.ordered source ->
 (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaGraph.reachable source root node dep -> active source root (SchemaGraph.key root node dep)=true.
Proof.
 intros Hordered Hroot Hreachable.
 destruct (SchemaGraph.reachable_grid source root node dep Hordered Hroot Hreachable) as [_ [Hdep _]].
 destruct (key_parts root node dep Hdep) as [Hnode Hdepth].
 unfold active. rewrite Hnode,Hdepth.
 destruct (List.in_dec _ (node,dep) (marked source root)) as [Hin|Hnot];[reflexivity|].
 exfalso. apply Hnot. exact (proj2 (SchemaMarkingSchedule.scheduled_marks_exact source root node dep Hordered Hroot) Hreachable).
Qed.
Lemma successor_mono kind bound dep bb cc dd : (bound<=SchemaEvaluationIndexCell.successor kind bound dep bb cc dd)%nat.
Proof.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[cbn [SchemaEvaluationIndexCell.successor];lia|cases rest index] end in cases 12%nat kind.
 reflexivity.
Qed.
Lemma advance_mono source root key before :
 (fst before<=fst (advance source root key before) /\ snd before<=snd (advance source root key before))%nat.
Proof.
 unfold advance. destruct (active source root key);[|split;reflexivity]. split;[cbn;lia|apply successor_mono].
Qed.
Lemma state_mono source root initialF initialB first last : (first<=last)%nat ->
 (fst (state source root initialF initialB first)<=fst (state source root initialF initialB last) /\
  snd (state source root initialF initialB first)<=snd (state source root initialF initialB last))%nat.
Proof.
 intro Hle. induction Hle as [|last Hle [HF HB]];[split;reflexivity|].
 pose proof (advance_mono source root last (state source root initialF initialB last)) as [HFstep HBstep].
 change (fst (state source root initialF initialB first)<=fst (advance source root last (state source root initialF initialB last)) /\
  snd (state source root initialF initialB first)<=snd (advance source root last (state source root initialF initialB last)))%nat. split;lia.
Qed.
Lemma formula_ceiling_step source root initialF initialB key :
 (formula_ceiling source root initialF initialB key<=formula_ceiling source root initialF initialB (S key))%nat.
Proof. apply (proj1 (state_mono source root initialF initialB _ _ (Nat.min_le_compat_r key (S key) (SchemaMarking.size root) ltac:(lia)))). Qed.
Lemma index_ceiling_step source root initialF initialB key :
 (index_ceiling source root initialF initialB key<=index_ceiling source root initialF initialB (S key))%nat.
Proof. apply (proj2 (state_mono source root initialF initialB _ _ (Nat.min_le_compat_r key (S key) (SchemaMarking.size root) ltac:(lia)))). Qed.
Lemma checked source root initialF initialB initialC : check source root initialF initialB initialC=true ->
 Z.of_nat (fst (state source root initialF initialB (SchemaMarking.size root)))<=SchemaEvaluationBoundedCell.bound /\
 Z.of_nat (snd (state source root initialF initialB (SchemaMarking.size root)))<=maximum /\
 forall key,(key<SchemaMarking.size root)%nat -> local_check source root initialF initialB initialC key=true.
Proof.
 unfold check. rewrite !Bool.andb_true_iff. intros [[HF HB] Hlocal].
 apply Z.leb_le in HF. apply Z.leb_le in HB. split;[exact HF|]. split;[exact HB|].
 intros key Hkey. apply (proj1 (forallb_forall _ _) Hlocal key). apply in_seq;lia.
Qed.
Lemma formula_ceiling_word source root initialF initialB initialC : check source root initialF initialB initialC=true ->
 forall key,Z.of_nat (formula_ceiling source root initialF initialB key)<=SchemaEvaluationBoundedCell.bound.
Proof.
 intros Hcheck key. destruct (checked source root initialF initialB initialC Hcheck) as [HF Hrest].
 pose proof (proj1 (state_mono source root initialF initialB (Nat.min key (SchemaMarking.size root)) (SchemaMarking.size root) (Nat.le_min_r _ _))) as Hbound.
 unfold formula_ceiling. lia.
Qed.
Lemma index_ceiling_word source root initialF initialB initialC : check source root initialF initialB initialC=true ->
 forall key,Z.of_nat (index_ceiling source root initialF initialB key)<=maximum.
Proof.
 intros Hcheck key. destruct (checked source root initialF initialB initialC Hcheck) as [_ [HB Hrest]].
 pose proof (proj2 (state_mono source root initialF initialB (Nat.min key (SchemaMarking.size root)) (SchemaMarking.size root) (Nat.le_min_r _ _))) as Hbound.
 unfold index_ceiling. lia.
Qed.
Theorem scalar source root initialF initialB initialC :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 check source root initialF initialB initialC=true ->
 SchemaEvaluationIndexReady.scalar (formula_ceiling source root initialF initialB) (index_ceiling source root initialF initialB) source root initialC.
Proof.
 intros Hordered Hroot Hcheck node dep kind aa bb cc dd expression Hreachable Hraw.
 destruct (SchemaGraph.reachable_grid source root node dep Hordered Hroot Hreachable) as [Hnode [Hdep Hkey]].
 pose proof (active_key source root node dep Hordered Hroot Hreachable) as Hactive.
 pose proof (descriptor_key source root node dep kind aa bb cc dd expression Hdep Hraw) as Hdescriptor.
 set (key:=SchemaGraph.key root node dep) in *.
 change (key<SchemaMarking.size root)%nat in Hkey.
 destruct (checked source root initialF initialB initialC Hcheck) as [_ [_ Hchecks]].
 specialize (Hchecks key Hkey). unfold local_check in Hchecks. rewrite Hactive,Hdescriptor in Hchecks. cbn [job_depth job_kind job_a job_b job_c job_d] in Hchecks.
 apply Bool.andb_true_iff in Hchecks. destruct Hchecks as [Hfuel Hclass].
 unfold formula_ceiling,index_ceiling.
 rewrite (Nat.min_l key (SchemaMarking.size root) ltac:(lia)),(Nat.min_l (S key) (SchemaMarking.size root) ltac:(lia)).
 assert (Hnext:state source root initialF initialB (S key)=
  (fst (state source root initialF initialB key)+SchemaEvaluationIndexBudget.cost (fst (state source root initialF initialB key)) kind aa dep,
   SchemaEvaluationIndexCell.successor kind (snd (state source root initialF initialB key)) dep bb cc dd)%nat).
 { cbn [state]. unfold advance. rewrite Hactive,Hdescriptor. reflexivity. }
 rewrite Hnext. cbn [fst snd]. split;[reflexivity|]. split.
 - intro Hrename. rewrite Hrename in Hfuel. now apply Z.leb_le.
 - split;[intro Hneeds;rewrite Hneeds in Hclass;now apply Z.leb_le|reflexivity].
Qed.
Theorem resources source logical root actual initialF initialB :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 (length (Protocol.formulas logical)<=initialF)%nat ->
 SchemaEvaluationIndexCell.bounded source (Protocol.formulas logical) (Protocol.classes logical) initialB ->
 check source root initialF initialB (length (Protocol.classes logical))=true ->
 SchemaInstanceGeneralReady.resources source logical root actual.
Proof.
 intros Hordered Hroot Hcapacity Hbounded Hcheck.
 exists (formula_ceiling source root initialF initialB),(index_ceiling source root initialF initialB).
 split;[exact (formula_ceiling_word source root initialF initialB _ Hcheck)|].
 split;[apply formula_ceiling_step|]. split;[exact (index_ceiling_word source root initialF initialB _ Hcheck)|].
 split;[apply index_ceiling_step|]. split;[exact Hcapacity|]. split;[exact Hbounded|].
 exact (scalar source root initialF initialB _ Hordered Hroot Hcheck).
Qed.
End SchemaEvaluationIndexSchedule.
