From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Lift Observation ArenaFrame RenameFrames Representation LocalParameters.
From Stdlib Require Import ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module IndexFrame.
Import IndexExecution SipHashExecution IndexSemantics.
Definition result_state s m i depth shift arg :=
  if bool_decide (i < depth) then store_meta s 0 i
  else store_meta (store_meta s 0 i) 0 (renamed_index m i depth shift arg).
Theorem generated s m i depth shift arg observations :
  (8 < length (memory s arraydef_0__meta))%nat -> word i -> word depth -> word shift -> word arg ->
  word (renamed_index m i depth shift arg) ->
  execObserved (funcdef_0__renameIndex (fun _ => false) (IndexExecution.arguments i depth (mode_number m) shift arg))
    (s,observations) = Some (tt,(result_state s m i depth shift arg,observations)).
Proof.
  intros Hmeta Hi Hd Hshift Harg Hresult. apply observed_plain; [apply InternalObservation.renameIndex_nf|].
  unfold result_state,renamed_index in *. case_bool_decide as Hbound.
  - now apply bound_variable.
  - apply free_variable; try assumption. lia.
Qed.
Definition native_arguments i depth mode shift arg : varsfuncdef_0__renameIndex -> Z :=
  update (update (update (update (update (fun _ => 0) vardef_0__renameIndex_index i)
    vardef_0__renameIndex_depth depth) vardef_0__renameIndex_mode mode)
    vardef_0__renameIndex_shift shift) vardef_0__renameIndex_arg arg.
Theorem generated_native s m i depth shift arg observations :
  (8 < length (memory s arraydef_0__meta))%nat -> word i -> word depth -> word shift -> word arg ->
  word (renamed_index m i depth shift arg) ->
  execObserved (funcdef_0__renameIndex (fun _ => false) (native_arguments i depth (mode_number m) shift arg))
    (s,observations) = Some (tt,(result_state s m i depth shift arg,observations)).
Proof.
  intros Hmeta Hi Hd Hshift Harg Hresult. unfold funcdef_0__renameIndex.
  rewrite (LocalParameters.observed_extensional funcdef_0__renameIndex_body
    (fun _ => false) (native_arguments i depth (mode_number m) shift arg)
    (fun _ => false) (IndexExecution.arguments i depth (mode_number m) shift arg) s observations
    ltac:(intros []; reflexivity) ltac:(intros []; reflexivity)).
  exact (generated s m i depth shift arg observations Hmeta Hi Hd Hshift Harg Hresult).
Qed.
Lemma result_meta_other s m i depth shift arg cell : cell <> 0%nat ->
  meta_value (result_state s m i depth shift arg) cell = meta_value s cell.
Proof. intros Hcell. unfold result_state. destruct (bool_decide (i < depth)); now repeat rewrite meta_store_other by exact Hcell. Qed.
Lemma result_meta_length s m i depth shift arg :
  length (memory (result_state s m i depth shift arg) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result_state. destruct (bool_decide (i < depth)); now repeat rewrite store_meta_length. Qed.
Lemma result_other s m i depth shift arg name : name <> arraydef_0__meta ->
  memory (result_state s m i depth shift arg) name = memory s name.
Proof. intros Hname. unfold result_state. destruct (bool_decide (i < depth)); now repeat rewrite store_meta_other by exact Hname. Qed.
Lemma result_value s m i depth shift arg : (0 < length (memory s arraydef_0__meta))%nat ->
  meta_value (result_state s m i depth shift arg) 0 = renamed_index m i depth shift arg.
Proof.
  intros Hmeta. unfold result_state,renamed_index. destruct (bool_decide (i < depth)); apply meta_store_same; try exact Hmeta.
  now rewrite store_meta_length.
Qed.
Lemma result_arena s m i depth shift arg fs : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena (result_state s m i depth shift arg) fs.
Proof.
  intros Harena. unfold result_state. destruct (bool_decide (i < depth)).
  - eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_meta; lia|exact Harena].
  - eapply ArenaFrame.storage_arena; [eapply ArenaFrame.storage_trans; apply ArenaFrame.storage_meta; lia|exact Harena].
Qed.
Lemma result_frames s m i depth shift arg fs stack : RenameFrames.represents s fs stack ->
  RenameFrames.represents (result_state s m i depth shift arg) fs stack.
Proof.
  intros Hrep. eapply RenameFrames.transport; [apply result_meta_other; lia|apply result_other; discriminate|exact Hrep].
Qed.
Theorem generated_semantics s m i depth shift arg observations :
  (8 < length (memory s arraydef_0__meta))%nat ->
  word (Z.of_nat i) -> word (Z.of_nat depth) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  execObserved (funcdef_0__renameIndex (fun _ => false)
    (IndexExecution.arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
    (s,observations) = Some (tt,(result_state s m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg),observations)) /\
  meta_value (result_state s m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)) 0 =
    Z.of_nat (under_binders depth (renaming m shift arg) i).
Proof.
  intros Hmeta Hi Hd Hshift Harg Hresult. rewrite <-index_semantics in Hresult |- *.
  split; [now apply generated|apply result_value; lia].
Qed.
End IndexFrame.
