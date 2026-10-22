From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternGrowth InternLengths FormulaEncoding Representation
  RenameStack RenameFrames RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant
  RenameMemoMeaning RenameMemoIntern RenameMemoJoin RenameMemoStorage RenameMemoAccounting Observation ObservedLocal.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoJoinRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Definition task phase p q depth left_value :=
  if Z.eq_dec phase 2 then RenameStack.right_done p q depth left_value else RenameStack.body_done p depth.
Definition parent phase p q := if Z.eq_dec phase 2 then SetTheory.implies p q else SetTheory.all p.
Definition joined phase left_value right_value :=
  if Z.eq_dec phase 2 then SetTheory.implies left_value right_value else SetTheory.all right_value.
Lemma fields fs raw phase p q depth left_value : (phase=2 \/ phase=3) ->
  RenameFrames.entry fs raw (task phase p q depth left_value) ->
  exists root left_id, raw=(root,Z.of_nat depth,phase,left_id) /\ word root /\ word (Z.of_nat depth) /\
    nth_error fs (Z.to_nat root)=Some (parent phase p q) /\
    (phase=2 -> word left_id /\ nth_error fs (Z.to_nat left_id)=Some left_value).
Proof.
  intros [Hphase|Hphase]; subst phase; destruct raw as [[[root raw_depth] raw_phase] left_id];
    cbn [task parent RenameFrames.entry].
  - intros [Hroot [Hdepth [-> [-> [Hparent [Hleft Hlookup]]]]]].
    exists root,left_id. split; [reflexivity|]. split; [exact Hroot|]. split; [exact Hdepth|].
    split; [exact Hparent|]. intros _; auto.
  - intros [Hroot [Hdepth [-> [-> Hparent]]]].
    exists root,left_id. split; [reflexivity|]. split; [exact Hroot|]. split; [exact Hdepth|].
    split; [exact Hparent|discriminate].
Qed.
Lemma arguments_spec phase fs left_id current left_value right_value : (phase = 2 \/ phase = 3) ->
  (phase = 2 -> word left_id /\ nth_error fs (Z.to_nat left_id) = Some left_value) ->
  word current -> nth_error fs (Z.to_nat current) = Some right_value ->
  FormulaEncoding.normal ((RenameMemoJoin.arguments phase left_id current) vardef_0__intern_tag,
    (RenameMemoJoin.arguments phase left_id current) vardef_0__intern_a,(RenameMemoJoin.arguments phase left_id current) vardef_0__intern_b) /\
  FormulaEncoding.decode fs ((RenameMemoJoin.arguments phase left_id current) vardef_0__intern_tag,
    (RenameMemoJoin.arguments phase left_id current) vardef_0__intern_a,(RenameMemoJoin.arguments phase left_id current) vardef_0__intern_b) =
    Some (joined phase left_value right_value).
Proof.
  intros Hphase Hleft Hcurrent Hlookup. destruct Hphase as [Hphase|Hphase]; subst phase.
  - destruct (Hleft eq_refl) as [Hleftword Hleftlookup].
    change (FormulaEncoding.normal (3,left_id,current) /\ FormulaEncoding.decode fs (3,left_id,current) = Some (SetTheory.implies left_value right_value)).
    split; [right; left; auto|]. unfold FormulaEncoding.decode. now rewrite Hleftlookup,Hlookup.
  - change (FormulaEncoding.normal (4,current,0) /\ FormulaEncoding.decode fs (4,current,0) = Some (SetTheory.all right_value)).
    split; [right; right; auto|]. change (option_map SetTheory.all (nth_error fs (Z.to_nat current)) = Some (SetTheory.all right_value)). now rewrite Hlookup.
Qed.
Lemma joined_renamed phase rho p q depth left_value right_value : (phase=2 \/ phase=3) ->
  (phase=2 -> left_value=RenameStack.renamed rho depth p /\ right_value=RenameStack.renamed rho depth q) ->
  (phase=3 -> right_value=RenameStack.renamed rho (S depth) p) ->
  joined phase left_value right_value=RenameStack.renamed rho depth (parent phase p q).
Proof.
  intros [Hphase|Hphase] Himp Hall; subst phase.
  - destruct (Himp eq_refl) as [-> ->]. reflexivity.
  - rewrite (Hall eq_refl). reflexivity.
Qed.
Theorem generated_join (f : Frame) phase fs rho p q depth stack left_value right_value current count observations :
  (phase=2 \/ phase=3) ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena (machine f) fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  RenameFrames.represents (machine f) fs (task phase p q depth left_value::stack) ->
  meta_value (machine f) 0=current -> word current -> nth_error fs (Z.to_nat current)=Some right_value ->
  (phase=2 -> left_value=RenameStack.renamed rho depth p /\ right_value=RenameStack.renamed rho depth q) ->
  (phase=3 -> right_value=RenameStack.renamed rho (S depth) p) ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  exists final next index size internstate,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning next rho) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (RenameStack.renamed rho depth (parent phase p q)) /\
    (exists extra, next=fs++extra) /\
    InternExecution.logical_frame (machine f) internstate /\
    RenameMemoInvariant.storage_frame internstate (machine final) /\ RenameMemoHit.parameters f final /\
    (length next<=S (length fs))%nat /\
    (forall root, word root -> nth_error fs (Z.to_nat root)=Some (parent phase p q) ->
      RenameMemoAccounting.completed (machine f) count (machine final) size (root,Z.of_nat depth)).
Proof.
  intros Hphase Hvalid Harena Hcapacity Hstack Hcurrent Hcurrentword Hlookup Himp Hall Hfits.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid) as Hmeta.
  pose proof (RenameMemoInvariant.error_clear _ _ _ Hvalid) as Herror.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct (fields fs raw phase p q depth left_value Hphase Hentry)
    as [root [left_id [-> [Hroot [Hdepth [Hparent Hleft]]]]]].
  assert (Hparentbound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnativebound : (Z.to_nat root<length (memory (machine f) arraydef_0__formulas))%nat).
  { pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  destruct (List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)) as [[tag a] b] eqn:Hformula.
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0)=
    (root,Z.of_nat depth,phase,left_id)) by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  destruct (arguments_spec phase fs left_id current left_value right_value Hphase Hleft Hcurrentword Hlookup) as [Hnormal Hdecode].
  destruct (RenameMemoIntern.generated (machine f) (fun _=>false) (RenameMemoJoin.arguments phase left_id current)
    fs (joined phase left_value right_value) count rho observations Hvalid Harena Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hnext [Hcache [Hindex [Hindexword [Hmeaning Hextends]]]]]]]]]].
  assert (Hplain : exec (funcdef_0__intern (fun _=>false) (RenameMemoJoin.arguments phase left_id current)) (machine f)=Some (tt,internstate)).
  { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) (RenameMemoJoin.arguments phase left_id current)) (machine f,observations)) as Herases. rewrite Hintern in Herases. exact (eq_sym Herases). }
  pose proof (InternGrowth.at_most_one (machine f) internstate _ _ fs next Harena Herror Hcapacity Hplain Hnext) as Hgrowth.
  pose proof (joined_renamed phase rho p q depth left_value right_value Hphase Himp Hall) as Hrenamed.
  assert (Hentrymeaning : RenameMemoMeaning.entry_meaning next rho (root,Z.of_nat depth) (meta_value internstate 0)).
  { rewrite Hindex. split; [exact Hroot|]. split; [exact Hdepth|]. split; [exact Hindexword|].
    exists (parent phase p q). split.
    - destruct Hextends as [extra ->]. now apply FormulaEncoding.nth_error_extend.
    - cbn [snd]. rewrite !Nat2Z.id. now rewrite <-Hrenamed.
  }
  assert (Hpostfits : Z.of_nat count/2<=meta_value internstate 30 -> Z.of_nat count<=9223372036854775807).
  { pose proof Hframe as [_ [Hm _]]. rewrite Hm by lia. exact Hfits. }
  destruct (RenameMemoAccounting.complete internstate root (Z.of_nat depth) (length stack) count
    (RenameMemoMeaning.entry_meaning next rho) observations Hcache Hpostfits Hentrymeaning)
    as (stored & size & Hput & Hchoice & Hstored & Hresult & Hpop & Hputframe & Hstorage & Hupper & Hnew & Hcovered).
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hcache) as Hpostmeta.
  pose proof (RenameMemoInvariant.error_clear _ _ _ Hcache) as Hposterror.
  exists (RenameMemoJoin.result f stored (length stack) root (Z.of_nat depth) phase left_id tag a b),next,index,size,internstate.
  split.
  - eapply RenameMemoJoin.generated_join_composition with (right_id:=current); eassumption.
  - split; [exact Hchoice|]. split; [exact Hstored|]. split.
    + now apply RenameMemoStorage.canonical_arena with (s:=internstate).
    + split.
      * apply RenameMemoStorage.popped_frames with (s:=internstate) (task:=task phase p q depth left_value); try assumption; [lia|].
        destruct Hframe as [Ha [Hm _]]. apply RenameFrames.transport with (s:=machine f).
        -- apply Hm; lia.
        -- apply Ha; discriminate.
        -- destruct Hextends as [extra ->]. now apply RenameFrames.extend.
      * split; [change (meta_value stored 0=Z.of_nat index); now rewrite Hresult|]. split; [exact Hindexword|]. split; [now rewrite <-Hrenamed|].
        split; [exact Hextends|]. split; [exact Hframe|]. split; [exact Hstorage|]. split; [apply RenameMemoJoin.parameters|].
        split; [exact Hgrowth|]. apply RenameMemoAccounting.completed_source with (root:=root).
        -- exact (proj1 (proj2 (proj2 Harena))).
        -- exact Hroot.
        -- exact Hparent.
        -- apply RenameMemoAccounting.completed_before with (middle:=internstate).
           ++ now apply RenameMemoAccounting.intern.
           ++ unfold RenameMemoAccounting.completed. auto.
Qed.
End RenameMemoJoinRefinement.
