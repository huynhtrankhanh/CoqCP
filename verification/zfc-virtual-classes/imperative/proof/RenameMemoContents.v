From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  RenameMemoInsert RenameMemoProbe RenameMemoGrow RenameMemoPut RenameMemoResize RenameMemoInvariant.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoContents.
Import IndexExecution SipHashExecution RenameMemoTable.
Local Opaque hash_state siphash24.
Definition has table size k := exists index, (index<size)%nat /\ occupied (table index)<>0 /\ matches (table index) k.
Definition covers before old_size after new_size := forall k, has before old_size k -> has after new_size k.
Lemma covers_trans first first_size second second_size third third_size :
  covers first first_size second second_size -> covers second second_size third third_size ->
  covers first first_size third third_size.
Proof. intros Hfirst Hsecond k Hhas. now apply Hsecond,Hfirst. Qed.
Lemma has_ext table other size k : (forall index, (index<size)%nat -> table index=other index) ->
  has table size k -> has other size k.
Proof. intros Hsame [index [Hindex [Hoccupied Hmatches]]]. exists index. split; [exact Hindex|]. now rewrite <-Hsame. Qed.
Lemma put_contains table size slot k result : (slot<size)%nat -> has (put table slot (fst k,snd k,result,1)) size k.
Proof.
  intro Hslot. exists slot. split; [exact Hslot|]. unfold put. destruct (numbers.Nat.eq_dec slot slot); [|contradiction].
  split; [discriminate|]. destruct k; split; reflexivity.
Qed.
Lemma put_covers table size slot k result : (slot<size)%nat ->
  (occupied (table slot)=0 \/ matches (table slot) k) -> covers table size (put table slot (fst k,snd k,result,1)) size.
Proof.
  intros Hslot Hplace query [index [Hindex [Hoccupied Hmatches]]].
  destruct (numbers.Nat.eq_dec index slot) as [->|Hdifferent].
  - destruct Hplace as [Hempty|Hkey]; [contradiction|].
    assert (Hsame : query=k).
    { destruct query as [qn qd], k as [kn kd]. destruct Hmatches as [Hqn Hqd], Hkey as [Hkn Hkd]. cbn in *. f_equal; congruence. }
    subst query. now apply put_contains.
  - exists index. split; [exact Hindex|]. unfold put. destruct (numbers.Nat.eq_dec index slot); [contradiction|]. auto.
Qed.
Theorem inserted s k result count slot : (0<count)%nat ->
  (count<=length (memory s arraydef_0__renameMemo))%nat -> RenameMemoInsert.placement s k count=Some slot ->
  has (RenameMemoLookup.table (RenameMemoInsert.result_state_below_half s k result count)) count k /\
  covers (RenameMemoLookup.table s) count (RenameMemoLookup.table (RenameMemoInsert.result_state_below_half s k result count)) count.
Proof.
  intros Hcount Hallocated Hplace.
  destruct (RenameMemoPlacement.place_sound (RenameMemoLookup.table s) count k (RenameMemoLookup.hash_start s k count) count slot
    Hcount (RenameMemoLookup.hash_start_bound s k count Hcount) Hplace) as [Hslot [Hentry Hpath]].
  pose proof (RenameMemoInsert.result_table s k result count slot Hcount Hallocated Hplace) as Htable.
  split.
  - apply has_ext with (table:=put (RenameMemoLookup.table s) slot (fst k,snd k,result,1));
      [intros; symmetry; apply Htable|now apply put_contains].
  - intros query Hhas. apply has_ext with (table:=put (RenameMemoLookup.table s) slot (fst k,snd k,result,1));
      [intros; symmetry; apply Htable|]. now apply put_covers.
Qed.
Theorem grown s t count meaning : RenameMemoGrow.postcondition s t count meaning ->
  covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) (2*count).
Proof.
  intros Hpost query [index [Hindex [Hoccupied Hmatches]]].
  destruct (RenameMemoGrow.post_covered _ _ _ _ Hpost index Hindex Hoccupied) as [slot [Hslot Hentry]].
  exists slot. split; [exact Hslot|]. rewrite Hentry. split; [discriminate|]. exact Hmatches.
Qed.
Theorem lookup_present s count k : RenameMemoLookup.indexed s count -> has (RenameMemoLookup.table s) count k ->
  exists result, RenameMemoLookup.lookup s k count=Some result.
Proof. intros Hindexed [index [Hindex [Hoccupied Hmatches]]]. now apply RenameMemoLookup.lookup_complete with (index:=index). Qed.
Theorem lookup_miss s count k : RenameMemoLookup.indexed s count -> RenameMemoLookup.lookup s k count=None ->
  ~has (RenameMemoLookup.table s) count k.
Proof. intros Hindexed Hmiss Hhas. destruct (lookup_present s count k Hindexed Hhas) as [value Hhit]. congruence. Qed.
Theorem below_half s t bs ns count observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (0<count)%nat ->
  Z.of_nat count<=maximum -> meta_value s 30<Z.of_nat count/2 ->
  (count<=length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) ->
  meta_value t 29=Z.of_nat count /\
  has (RenameMemoLookup.table t) count (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) /\
  covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) count.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcapacity Hcount Hword Hload Hallocated Hlive Hrun.
  pose proof (RenameMemoInsert.generated_below_half s bs ns count observations Hmeta Hsip Hpositive Herror Hcapacity Hcount Hword Hload Hallocated) as Hexact.
  rewrite Hrun in Hexact. injection Hexact as ->.
  destruct (RenameMemoInsert.placement_available s (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) count Hcount
    (RenameMemoInsert.below_half_room s count Hlive Hload)) as [slot Hplace].
  split.
  - destruct (RenameMemoInsert.result_frame s (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth)
      (ns vardef_0__renameCachePut_value) count) as [_ [Hm _]]. rewrite Hm by lia. exact Hcapacity.
  - now apply inserted with (slot:=slot).
Qed.
Theorem executed s t bs ns count observations meaning : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) ->
  exists size, meta_value t 29=Z.of_nat size /\
    has (RenameMemoLookup.table t) size (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) /\
    covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) size.
Proof.
  intros Hvalid Hfits Hrun.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity Hmin Hword Hallocated Hlive Hload Hmeaning Hindexed].
  destruct (Z_lt_dec (meta_value s 30) (Z.of_nat count/2)) as [Hsmall|Hlarge].
  - exists count. now apply below_half with (s:=s) (bs:=bs) (ns:=ns) (observations:=observations); try assumption; lia.
  - assert (Hdouble : Z.of_nat count<=9223372036854775807) by (apply Hfits; lia).
    destruct (RenameMemoGrow.generated_invariant s (fun _=>false) (fun _=>0) count observations meaning Hmeta Hsip Hpositive Herror
      Hcapacity ltac:(lia) Hdouble Hallocated Hmeaning) as [resized [Hresize Hpost]].
    pose proof (RenameMemoGrow.post_frame _ _ _ _ Hpost) as [Ha [Hm [Hl [Hs [Hi Ho]]]]].
    assert (Hrmeta : (31<length (memory resized arraydef_0__meta))%nat) by now rewrite Hl.
    assert (Hrsip : (0<length (memory resized arraydef_0__sipState))%nat) by now rewrite Hs.
    assert (Hrpositive : 0<meta_value resized 20) by (rewrite Hm by lia; exact Hpositive).
    assert (Hrlive : meta_value resized 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table resized) (2*count))).
    { rewrite Hm by lia. rewrite (RenameMemoGrow.post_live _ _ _ _ Hpost). exact Hlive. }
    assert (Hhalf : Z.of_nat (2*count)/2=Z.of_nat count).
    { rewrite <-RenameMemoResize.double_value,Z.div_mul by lia. reflexivity. }
    assert (Hrload : meta_value resized 30<Z.of_nat (2*count)/2).
    { rewrite Hm by lia. rewrite Hhalf. pose proof (Z.div_mod (Z.of_nat count) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (Z.of_nat count) 2 ltac:(lia)). lia. }
    assert (Hrword : Z.of_nat (2*count)<=maximum).
    { rewrite <-RenameMemoResize.double_value. exact (proj2 (RenameMemoResize.double_word count Hdouble)). }
    assert (Hrrun : execObserved (funcdef_0__renameCachePut bs ns) (resized,observations)=Some (tt,(t,observations))).
    { rewrite <- (RenameMemoPut.generated_resize_composition s resized bs ns observations Hmeta Hrmeta
        ltac:(rewrite Hcapacity; lia) ltac:(rewrite (RenameMemoGrow.post_capacity _ _ _ _ Hpost); exact Hrload) Hresize). exact Hrun. }
    destruct (below_half resized t bs ns (2*count)%nat observations Hrmeta Hrsip Hrpositive
      (RenameMemoGrow.post_nonfatal _ _ _ _ Hpost) (RenameMemoGrow.post_capacity _ _ _ _ Hpost) ltac:(lia) Hrword Hrload
      (RenameMemoGrow.post_allocated _ _ _ _ Hpost) Hrlive Hrrun) as [Hfinalsize [Hnew Hcovers]].
    exists (2*count)%nat. split; [exact Hfinalsize|]. split; [exact Hnew|].
    apply covers_trans with (second:=RenameMemoLookup.table resized) (second_size:=(2*count)%nat);
      [now apply grown with (meaning:=meaning)|exact Hcovers].
Qed.
Theorem generated s bs ns count observations meaning : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) (ns vardef_0__renameCachePut_value) ->
  exists t size, execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid t size meaning /\ RenameMemoPut.storage_frame s t /\
    has (RenameMemoLookup.table t) size (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) /\
    covers (RenameMemoLookup.table s) count (RenameMemoLookup.table t) size.
Proof.
  intros Hvalid Hfits Hmeaning.
  destruct (RenameMemoInvariant.generated_put s bs ns count observations meaning Hvalid Hfits Hmeaning)
    as [t [size [Hrun [Hchoice [Hnext Hframe]]]]].
  destruct (executed s t bs ns count observations meaning Hvalid Hfits Hrun) as [actual [Hcapacity [Hnew Hcovers]]].
  assert (Hsame : actual=size) by (pose proof (RenameMemoInvariant.capacity_value _ _ _ Hnext); lia).
  subst actual. exists t,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hnext|]. split; [exact Hframe|]. split; assumption.
Qed.
End RenameMemoContents.
