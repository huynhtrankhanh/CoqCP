From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift IndexFrame Intern InternGrowth InternLengths FormulaEncoding Representation
  RenameStack RenameFrames RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoTable RenameMemoLookup RenameMemoInvariant
  RenameMemoMeaning RenameMemoVisit RenameMemoHitRefinement RenameMemoIntern RenameMemoJoin RenameMemoAtom RenameMemoIndex RenameMemoStorage
  RenameMemoAccounting Observation ObservedLocal.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoAtomRefinement.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameMemoInit RenameMemoControl.
Definition atom tag i j := if Z.eq_dec tag 1 then SetTheory.equal i j else SetTheory.member i j.
Lemma decoded fs tag i j : (tag = 1 \/ tag = 2) ->
  FormulaEncoding.decode fs (tag,Z.of_nat i,Z.of_nat j) = Some (atom tag i j).
Proof. intros Htag. destruct Htag as [Htag|Htag]; subst tag; unfold atom,FormulaEncoding.decode; now rewrite !Nat2Z.id. Qed.
Lemma normal tag i j : (tag = 1 \/ tag = 2) -> word (Z.of_nat i) -> word (Z.of_nat j) ->
  FormulaEncoding.normal (tag,Z.of_nat i,Z.of_nat j).
Proof. intros Htag Hi Hj. right. left. split; [tauto|auto]. Qed.
Lemma renamed_atom tag i j rho : (tag = 1 \/ tag = 2) ->
  SetTheory.rename rho (atom tag i j) = atom tag (rho i) (rho j).
Proof. intros Htag. destruct Htag as [Htag|Htag]; subst tag; reflexivity. Qed.
Theorem generated_atom_miss (f : Frame) tag fs i j depth stack m shift arg count root left_id observations :
  (tag=1 \/ tag=2) ->
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)) ->
  NativeRepresentation.canonical_arena (machine f) fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (atom tag i j) depth::stack) ->
  RenameMemoVisit.view (machine f) fs (atom tag i j) depth stack root left_id ->
  RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count=None ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) j)) ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  exists final next index size,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (RenameStack.renamed (renaming m shift arg) depth (atom tag i j)) /\
    (exists extra, next=fs++extra) /\ RenameMemoHit.parameters f final /\ (length next<=S (length fs))%nat /\
    RenameMemoAccounting.completed (machine f) count (machine final) size (root,Z.of_nat depth).
Proof.
  intros Htag Hmode Hshift Harg Hvalid Harena Hcapacity Hstack Hview Hnone Hi Hj Hshiftword Hargword Hmapped_i Hmapped_j Hfits.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity0 Hmin HcapWord Hmemo Hlive Hload Hentries Hindexed].
  destruct Hview as [Hcount Hcountword Hroot Hdepth Hframes Hnth Hlookup Hnativebound].
  assert (Hsourcebound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hformula : List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)=(tag,Z.of_nat i,Z.of_nat j)).
  { apply (FormulaEncoding.decode_injective fs _ _ (atom tag i j) (proj1 (proj2 (proj2 Harena)))).
    - exact (proj2 (proj2 (proj2 Harena)) _ Hsourcebound).
    - now apply normal.
    - exact (NativeRepresentation.represented_lookup _ _ _ _ (proj1 (proj2 Harena)) Hlookup).
    - now apply decoded. }
  set (looked:=RenameMemoLookup.result_state (machine f) (root,Z.of_nat depth) count).
  assert (Hlookvalid : RenameMemoInvariant.valid looked count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoInvariant.lookup_valid.
  assert (Hget : execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)))
    (machine f,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact (machine f) (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)) count observations
      Hmeta Hsip Hpositive Hcapacity0 ltac:(lia) HcapWord Hmemo) as Hrun.
    cbv beta iota zeta delta [RenameMemoHit.arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hmiss : meta_value looked 31=maximum).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hnone by exact Hmeta. reflexivity. }
  assert (Hlookarena : NativeRepresentation.canonical_arena looked fs).
  { apply RenameMemoStorage.canonical_arena with (s:=machine f); [apply RenameMemoInvariant.lookup_storage|exact Harena]. }
  assert (Hlookframes : RenameFrames.represents looked fs (RenameStack.visit (atom tag i j) depth::stack)).
  { pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [Ha [Hm _]].
    apply RenameFrames.transport with (s:=machine f); [apply Hm; lia|apply Ha; discriminate|exact Hstack]. }
  set (first:=IndexFrame.result_state looked m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (second:=IndexFrame.result_state first m (Z.of_nat j) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (mapped_i:=under_binders depth (renaming m shift arg) i).
  set (mapped_j:=under_binders depth (renaming m shift arg) j).
  assert (Hfirstvalid : RenameMemoInvariant.valid first count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoIndex.index_valid.
  assert (Hsecondvalid : RenameMemoInvariant.valid second count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoIndex.index_valid.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid) as Hlookmeta.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hfirstvalid) as Hfirstmeta.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hsecondvalid) as Hsecondmeta.
  assert (Hfirst : execObserved (funcdef_0__renameIndex (fun _=>false)
    (IndexFrame.native_arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
    (looked,observations)=Some (tt,(first,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hfirstvalue : meta_value first 0=Z.of_nat mapped_i).
  { unfold first,mapped_i. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecond : execObserved (funcdef_0__renameIndex (fun _=>false)
    (IndexFrame.native_arguments (Z.of_nat j) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
    (first,observations)=Some (tt,(second,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hsecondvalue : meta_value second 0=Z.of_nat mapped_j).
  { unfold second,mapped_j. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecondarena : NativeRepresentation.canonical_arena second fs)
    by (apply IndexFrame.result_arena; now apply IndexFrame.result_arena).
  assert (Hsecondframes : RenameFrames.represents second fs (RenameStack.visit (atom tag i j) depth::stack))
    by (apply IndexFrame.result_frames; now apply IndexFrame.result_frames).
  assert (Hnormal : FormulaEncoding.normal (tag,Z.of_nat mapped_i,Z.of_nat mapped_j)) by now apply normal.
  pose proof (decoded fs tag mapped_i mapped_j Htag) as Hdecode.
  destruct (RenameMemoIntern.generated second (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j))
    fs (atom tag mapped_i mapped_j) count (renaming m shift arg) observations Hsecondvalid Hsecondarena Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hnext [Hcache [Hindex [Hindexword [Hmeaning Hextends]]]]]]]]]].
  assert (Hplain : exec (funcdef_0__intern (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)))
    second=Some (tt,internstate)).
  { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j))) (second,observations)) as Herases. rewrite Hintern in Herases. exact (eq_sym Herases). }
  pose proof (InternGrowth.at_most_one second internstate _ _ fs next Hsecondarena
    (RenameMemoInvariant.error_clear _ _ _ Hsecondvalid) Hcapacity Hplain Hnext) as Hgrowth.
  assert (Hrenamed : atom tag mapped_i mapped_j=RenameStack.renamed (renaming m shift arg) depth (atom tag i j)).
  { symmetry. apply renamed_atom. exact Htag. }
  assert (Hentrymeaning : RenameMemoMeaning.entry_meaning next (renaming m shift arg) (root,Z.of_nat depth) (meta_value internstate 0)).
  { rewrite Hindex. split; [exact Hroot|]. split; [exact Hdepth|]. split; [exact Hindexword|]. exists (atom tag i j). split.
    - destruct Hextends as [extra ->]. now apply FormulaEncoding.nth_error_extend.
    - cbn [snd]. rewrite !Nat2Z.id. now rewrite <-Hrenamed. }
  assert (Hpostfits : Z.of_nat count/2<=meta_value internstate 30 -> Z.of_nat count<=9223372036854775807).
  { pose proof Hframe as [_ [Hm _]]. rewrite Hm by lia. unfold second,first.
    rewrite !IndexFrame.result_meta_other by lia. unfold looked.
    pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [_ [Hlookupmeta _]].
    rewrite Hlookupmeta by lia. exact Hfits. }
  destruct (RenameMemoAccounting.complete internstate root (Z.of_nat depth) (length stack) count
    (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) observations Hcache Hpostfits Hentrymeaning)
    as (stored & size & Hput & Hchoice & Hstored & Hresult & Hpop & Hputframe & Hstorage & Hupper & Hnew & Hcovered).
  exists (RenameMemoAtom.result f stored (length stack) root (Z.of_nat depth) left_id tag (Z.of_nat i) (Z.of_nat j)
    (Z.of_nat mapped_i) (Z.of_nat mapped_j)),next,index,size. split.
  - eapply RenameMemoAtom.generated_atom_composition with (looked:=looked) (first:=first) (second:=second)
      (mode:=mode_number m) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + exact (RenameMemoInvariant.error_clear _ _ _ Hlookvalid).
    + exact (RenameMemoInvariant.metadata_ready _ _ _ Hcache).
    + exact (RenameMemoInvariant.error_clear _ _ _ Hcache).
  - split; [exact Hchoice|]. split; [exact Hstored|]. split.
    + now apply RenameMemoStorage.canonical_arena with (s:=internstate).
    + split.
      * apply RenameMemoStorage.popped_frames with (s:=internstate) (task:=RenameStack.visit (atom tag i j) depth); try assumption.
        -- pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hcache). lia.
        -- destruct Hframe as [Ha [Hm _]]. apply RenameFrames.transport with (s:=second).
           ++ apply Hm; lia.
           ++ apply Ha; discriminate.
           ++ destruct Hextends as [extra ->]. now apply RenameFrames.extend.
      * split; [change (meta_value stored 0=Z.of_nat index); now rewrite Hresult|]. split; [exact Hindexword|].
        split; [now rewrite <-Hrenamed|]. split; [exact Hextends|]. split; [apply RenameMemoAtom.parameters|].
        split; [exact Hgrowth|]. apply RenameMemoAccounting.completed_before with (middle:=internstate).
        -- apply RenameMemoAccounting.passive_trans with (t:=looked); [apply RenameMemoAccounting.lookup|].
           apply RenameMemoAccounting.passive_trans with (t:=first); [apply RenameMemoAccounting.index|].
           apply RenameMemoAccounting.passive_trans with (t:=second); [apply RenameMemoAccounting.index|].
           exact (RenameMemoAccounting.intern second internstate Hframe).
        -- unfold RenameMemoAccounting.completed. auto.
Qed.
Theorem generated_atom (f : Frame) tag fs i j depth stack m shift arg count observations :
  (tag=1 \/ tag=2) ->
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)) ->
  NativeRepresentation.canonical_arena (machine f) fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (atom tag i j) depth::stack) ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) j)) ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  exists final next index size,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (RenameStack.renamed (renaming m shift arg) depth (atom tag i j)) /\
    (exists extra, next=fs++extra) /\ RenameMemoHit.parameters f final /\ (length next<=S (length fs))%nat.
Proof.
  intros Htag Hmode Hshift Harg Hvalid Harena Hcapacity Hstack Hi Hj Hshiftword Hargword Hmapped_i Hmapped_j Hfits.
  destruct (RenameMemoVisit.top_visit (machine f) fs (atom tag i j) depth stack Harena Hstack) as [root [left_id Hview]].
  destruct (RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count) as [value|] eqn:Hlookup.
  - assert (Hmeaning : RenameMemoMeaning.entry_meaning fs (renaming m shift arg) (root,Z.of_nat depth) value).
    { exact (RenameMemoTable.scan_meaning (RenameMemoLookup.table (machine f)) count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg))
        (root,Z.of_nat depth) (RenameMemoLookup.hash_start (machine f) (root,Z.of_nat depth) count) count value
        ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia)
        (RenameMemoLookup.hash_start_bound (machine f) (root,Z.of_nat depth) count ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia))
        (RenameMemoInvariant.entries_mean _ _ _ Hvalid) Hlookup). }
    pose proof Hmeaning as [_ [_ [Hvalueword _]]].
    destruct (RenameMemoHitRefinement.generated_cached_visit f fs (renaming m shift arg) (atom tag i j) depth stack count root left_id value observations
      Hvalid Harena Hstack Hview Hlookup) as (final & Hrun & Hvalid' & Harena' & Hframes' & Hresult & Hdenotes & Hstorage & Hparameters & Hpassive).
    exists final,fs,(Z.to_nat value),count. split; [exact Hrun|]. split; [now left|]. split; [exact Hvalid'|]. split; [exact Harena'|].
    split; [exact Hframes'|]. split; [rewrite Z2Nat.id by exact (proj1 Hvalueword); exact Hresult|].
    split; [rewrite Z2Nat.id by exact (proj1 Hvalueword); exact Hvalueword|].
    split; [rewrite Hresult in Hdenotes; exact Hdenotes|]. split; [exists []; now rewrite app_nil_r|]. split; [exact Hparameters|lia].
  - destruct (generated_atom_miss f tag fs i j depth stack m shift arg count root left_id observations Htag Hmode Hshift Harg
      Hvalid Harena Hcapacity Hstack Hview Hlookup Hi Hj Hshiftword Hargword Hmapped_i Hmapped_j Hfits)
      as (final & next & index & size & Hpost).
    exists final,next,index,size. tauto.
Qed.
End RenameMemoAtomRefinement.
