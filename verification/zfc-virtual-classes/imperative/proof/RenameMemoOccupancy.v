From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoCapacity RenameMemoInsert
  RenameMemoGrow RenameMemoPut RenameMemoResize RenameMemoInvariant RenameMemoBounds RenameMemoResourceBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoOccupancy.
Import IndexExecution SipHashExecution.
Local Opaque hash_state siphash24.
Theorem below_half s t bs ns count observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (0<count)%nat ->
  Z.of_nat count<=maximum -> meta_value s 30<Z.of_nat count/2 ->
  (count<=length (memory s arraydef_0__renameMemo))%nat ->
  meta_value s 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table s) count) ->
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) ->
  meta_value t 30<=meta_value s 30+1.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcapacity Hcount Hword Hload Hallocated Hlive Hrun.
  pose proof (RenameMemoInsert.generated_below_half s bs ns count observations Hmeta Hsip Hpositive Herror Hcapacity Hcount Hword Hload Hallocated) as Hexact.
  rewrite Hrun in Hexact. injection Hexact as ->.
  destruct (RenameMemoInsert.placement_available s (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) count Hcount
    (RenameMemoInsert.below_half_room s count Hlive Hload)) as [slot Hplace].
  rewrite (RenameMemoInsert.result_live_count s _ _ count slot Hmeta Hcount Hallocated Hplace Hlive
    (RenameMemoInsert.below_half_increment_word s count Hword Hlive Hload)).
  pose proof (RenameMemoPut.result_live_upper s (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth)
    (ns vardef_0__renameCachePut_value) count slot Hcount Hallocated Hplace) as Hupper. lia.
Qed.
Theorem executed s t bs ns count observations meaning : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) ->
  meta_value t 30<=meta_value s 30+1.
Proof.
  intros Hvalid Hfits Hrun.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity Hmin Hword Hallocated Hlive Hload Hmeaning Hindexed].
  destruct (Z_lt_dec (meta_value s 30) (Z.of_nat count/2)) as [Hsmall|Hlarge].
  - now apply below_half with (s:=s) (count:=count) (bs:=bs) (ns:=ns) (observations:=observations); try assumption; lia.
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
    pose proof (below_half resized t bs ns (2*count)%nat observations Hrmeta Hrsip Hrpositive
      (RenameMemoGrow.post_nonfatal _ _ _ _ Hpost) (RenameMemoGrow.post_capacity _ _ _ _ Hpost) ltac:(lia) Hrword Hrload
      (RenameMemoGrow.post_allocated _ _ _ _ Hpost) Hrlive Hrrun) as Hupper.
    rewrite Hm in Hupper by lia. exact Hupper.
Qed.
Theorem generated s bs ns count observations meaning : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (ns vardef_0__renameCachePut_node,ns vardef_0__renameCachePut_depth) (ns vardef_0__renameCachePut_value) ->
  exists t size, execObserved (funcdef_0__renameCachePut bs ns) (s,observations)=Some (tt,(t,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid t size meaning /\ RenameMemoPut.storage_frame s t /\
    meta_value t 30<=meta_value s 30+1.
Proof.
  intros Hvalid Hfits Hmeaning.
  destruct (RenameMemoInvariant.generated_put s bs ns count observations meaning Hvalid Hfits Hmeaning)
    as [t [size [Hrun [Hchoice [Hnext Hframe]]]]].
  exists t,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hnext|]. split; [exact Hframe|].
  now apply executed with (bs:=bs) (ns:=ns) (count:=count) (observations:=observations) (meaning:=meaning).
Qed.
Theorem budget_growth s count meaning root : RenameMemoInvariant.valid s count meaning ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> meta_value s 30<=Z.of_nat (S root*S root) ->
  Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807.
Proof.
  intros Hvalid Hfuel Hlive Hgrow. exact (RenameMemoResourceBounds.growth_safe root (Z.of_nat count) (meta_value s 30)
    Hfuel ltac:(lia) Hlive Hgrow).
Qed.
End RenameMemoOccupancy.
