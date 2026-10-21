From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoCapacity RenameMemoInit RenameMemoHit
  RenameMemoPut RenameMemoRebuild RenameMemoResize ObservedLocal Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoInvariant.
Import IndexExecution SipHashExecution.
Local Opaque hash_state.
Record valid s count meaning : Prop := {
  metadata_ready : (31<length (memory s arraydef_0__meta))%nat;
  sip_ready : (0<length (memory s arraydef_0__sipState))%nat;
  buckets_positive : 0<meta_value s 20;
  error_clear : meta_value s 8=0;
  capacity_value : meta_value s 29=Z.of_nat count;
  capacity_minimum : (2<=count)%nat;
  capacity_word : Z.of_nat count<=maximum;
  capacity_allocated : (count<=length (memory s arraydef_0__renameMemo))%nat;
  live_accurate : meta_value s 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count);
  half_loaded : meta_value s 30<=Z.of_nat count/2;
  entries_mean : RenameMemoTable.represents (RenameMemoLookup.table s) count meaning;
  entries_indexed : RenameMemoLookup.indexed s count
}.
Theorem initialized s meaning : (31<length (memory s arraydef_0__meta))%nat ->
  (0<length (memory s arraydef_0__sipState))%nat -> 0<meta_value s 20 -> meta_value s 8=0 ->
  valid (RenameMemoInit.initialized s) 16 meaning.
Proof.
  intros Hmeta Hsip Hpositive Herror. constructor.
  - now rewrite RenameMemoInit.initialized_meta_length.
  - now rewrite RenameMemoInit.initialized_other by discriminate.
  - now rewrite RenameMemoInit.initialized_meta_other by lia.
  - now rewrite RenameMemoInit.initialized_meta_other by lia.
  - now apply RenameMemoInit.initialized_size.
  - lia.
  - unfold maximum. cbn. lia.
  - apply RenameMemoInit.initialized_capacity.
  - rewrite RenameMemoInit.initialized_count by exact Hmeta. now rewrite RenameMemoInit.initialized_live.
  - rewrite RenameMemoInit.initialized_count by exact Hmeta. apply Z.div_pos; lia.
  - apply RenameMemoInit.initialized_meaning.
  - apply RenameMemoInit.initialized_indexed.
Qed.
Theorem transport s t count meaning : valid s count meaning -> RenameMemoHit.storage_frame s t ->
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) -> valid t count meaning.
Proof.
  intros Hvalid Hframe Hsip. pose proof (RenameMemoHit.frame_table s t Hframe) as Htable.
  assert (Hhash : forall query, RenameMemoLookup.hash_start t query count=RenameMemoLookup.hash_start s query count).
  { intro query. exact (RenameMemoHit.frame_hash s t count query Hframe). }
  destruct Hframe as [Ha [Hm [Hl [Hi Ho]]]]. destruct Hvalid as [Hmeta Hsip0 Hpositive Herror Hcount Hmin Hword Hallocated Hlive Hload Hmeaning Hindexed].
  constructor.
  - now rewrite Hl.
  - now rewrite Hsip.
  - now rewrite Hm by lia.
  - now rewrite Hm by lia.
  - now rewrite Hm by lia.
  - assumption.
  - assumption.
  - now rewrite Ha by discriminate.
  - now rewrite Hm,Htable by lia.
  - now rewrite Hm by lia.
  - now rewrite Htable.
  - intros index Hindex Hoccupied. rewrite Htable in Hoccupied |- *.
    rewrite Hhash. now apply Hindexed.
Qed.
Lemma lookup_frame s key count : RenameMemoHit.storage_frame s (RenameMemoLookup.result_state s key count).
Proof.
  destruct (RenameMemoLookup.result_frame s key count) as [Ha [Hm [Hl [Hi Ho]]]].
  split; [exact Ha|]. split; [intros; now apply Hm|]. repeat split; assumption.
Qed.
Lemma lookup_sip_length s key count :
  length (memory (RenameMemoLookup.result_state s key count) arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  assert (Hhash : forall original, length (memory (hash_state original 5 (fst key) (snd key)) arraydef_0__sipState)=
    length (memory original arraydef_0__sipState)).
  { intro original. exact (RenameMemoRebuild.hashed_sip_length original (fst key,snd key,0,0)). }
  unfold RenameMemoLookup.result_state. destruct (RenameMemoLookup.lookup s key count);
    [rewrite store_meta_other by discriminate|]; unfold RenameMemoLookup.prepared;
    rewrite Hhash; now rewrite store_meta_other by discriminate.
Qed.
Theorem lookup_valid s key count meaning : valid s count meaning -> valid (RenameMemoLookup.result_state s key count) count meaning.
Proof. intro Hvalid. exact (transport s _ count meaning Hvalid (lookup_frame s key count) (lookup_sip_length s key count)). Qed.
Definition completed s top value:=store_meta (store_meta s 0 value) 10 (Z.of_nat top).
Lemma completed_frame s top value : RenameMemoHit.storage_frame s (completed s top value).
Proof.
  unfold completed. split; [intros; now rewrite !store_meta_other by assumption|].
  split; [intros; now rewrite !meta_store_other by assumption|]. split; [now rewrite !store_meta_length|]. split; reflexivity.
Qed.
Theorem completed_valid s top value count meaning : valid s count meaning -> valid (completed s top value) count meaning.
Proof.
  intro Hvalid. apply transport with (s:=s); [exact Hvalid|apply completed_frame|].
  unfold completed. now rewrite !store_meta_other by discriminate.
Qed.
Theorem inserted_valid s t count size meaning : valid s count meaning -> RenameMemoPut.postcondition s t size meaning ->
  (2<=size)%nat -> Z.of_nat size<=maximum -> valid t size meaning.
Proof.
  intros Hvalid Hpost Hsize Hword.
  destruct (RenameMemoPut.post_frame _ _ _ _ Hpost) as [Ha [Hm [Hl [Hs [Hi Ho]]]]].
  constructor.
  - rewrite Hl. exact (metadata_ready _ _ _ Hvalid).
  - rewrite Hs. exact (sip_ready _ _ _ Hvalid).
  - rewrite Hm by lia. exact (buckets_positive _ _ _ Hvalid).
  - exact (RenameMemoPut.post_nonfatal _ _ _ _ Hpost).
  - exact (RenameMemoPut.post_capacity _ _ _ _ Hpost).
  - exact Hsize.
  - exact Hword.
  - exact (RenameMemoPut.post_allocated _ _ _ _ Hpost).
  - exact (RenameMemoPut.post_live _ _ _ _ Hpost).
  - exact (RenameMemoPut.post_load _ _ _ _ Hpost).
  - exact (RenameMemoPut.post_meaning _ _ _ _ Hpost).
  - exact (RenameMemoPut.post_indexed _ _ _ _ Hpost).
Qed.
Theorem generated_put s bs ns count observations meaning : valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) (ns vardef_0__renameCachePut_value) ->
  exists t size, execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ valid t size meaning /\ RenameMemoPut.storage_frame s t.
Proof.
  intros Hvalid Hfits Hmeaning. pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcount Hmin Hword Hmemo Hlive Hload Hentries Hindexed].
  destruct (Z_lt_dec (meta_value s 30) (Z.of_nat count/2)) as [Hsmall|Hlarge].
  - destruct (RenameMemoPut.generated_below_half_contract s bs ns count observations meaning Hmeta Hsip Hpositive Herror Hcount
      ltac:(lia) Hword Hsmall Hmemo Hlive Hentries Hmeaning Hindexed) as [t [Hrun Hpost]].
    exists t,count. split; [exact Hrun|]. split; [now left|]. split.
    + exact (inserted_valid s t count count meaning Hvalid Hpost Hmin Hword).
    + exact (RenameMemoPut.post_frame _ _ _ _ Hpost).
  - assert (Hdouble : Z.of_nat count<=9223372036854775807) by (apply Hfits; lia).
    destruct (RenameMemoPut.generated_invariant s bs ns count observations meaning Hmeta Hsip Hpositive Herror Hcount Hmin Hdouble
      Hload Hmemo Hlive Hentries Hmeaning Hindexed) as [t [size [Hrun [Hchoice Hpost]]]].
    exists t,size. split; [exact Hrun|]. split; [exact Hchoice|]. split.
    + apply inserted_valid with (s:=s) (count:=count); try assumption.
      * destruct Hchoice as [->| ->]; lia.
      * destruct Hchoice as [->| ->]; [exact Hword|]. rewrite <-RenameMemoResize.double_value.
        exact (proj2 (RenameMemoResize.double_word count Hdouble)).
    + exact (RenameMemoPut.post_frame _ _ _ _ Hpost).
Qed.
Definition storage_frame s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__sipState -> name<>arraydef_0__renameMemo ->
    name<>arraydef_0__renameMemoScratch -> memory t name=memory s name) /\
  (forall cell, cell<>0%nat -> cell<>8%nat -> cell<>10%nat -> cell<>21%nat -> cell<>28%nat ->
    cell<>29%nat -> cell<>30%nat -> cell<>31%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) /\
  stdin t=stdin s /\ stdout t=stdout s.
Lemma storage_trans s t u : storage_frame s t -> storage_frame t u -> storage_frame s u.
Proof.
  intros [Ha [Hm [Hl [Hs [Hi Ho]]]]] [Ha' [Hm' [Hl' [Hs' [Hi' Ho']]]]].
  split; [intros; now rewrite Ha',Ha by assumption|]. split; [intros; now rewrite Hm',Hm by assumption|]. repeat split; congruence.
Qed.
Lemma lookup_storage s key count : storage_frame s (RenameMemoLookup.result_state s key count).
Proof.
  destruct (RenameMemoLookup.result_frame s key count) as [Ha [Hm [Hl [Hi Ho]]]].
  split; [intros; now apply Ha|]. split; [intros; now apply Hm|].
  split; [exact Hl|]. split; [apply lookup_sip_length|]. split; assumption.
Qed.
Lemma completed_storage s top value : storage_frame s (completed s top value).
Proof.
  unfold completed. split; [intros; now rewrite !store_meta_other by assumption|].
  split; [intros; now rewrite !meta_store_other by assumption|].
  split; [now rewrite !store_meta_length|]. split; [now rewrite !store_meta_other by discriminate|]. split; reflexivity.
Qed.
Lemma inserted_storage s t : RenameMemoPut.storage_frame s t -> storage_frame s t.
Proof.
  intros [Ha [Hm [Hl [Hs [Hi Ho]]]]]. split; [exact Ha|]. split; [intros; now apply Hm|]. repeat split; assumption.
Qed.
End RenameMemoInvariant.
