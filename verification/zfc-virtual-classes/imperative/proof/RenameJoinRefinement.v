From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternBounded InternGrowth Observation ObservedLocal RenameStack RenameFrames RenameStructure RenameJoin FormulaEncoding Representation HashTable ArenaFrame RenameConfiguration.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameJoinRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Definition task phase p q depth left_value := if Z.eq_dec phase 2 then RenameStack.right_done p q depth left_value else RenameStack.body_done p depth.
Definition joined phase left_value right_value := if Z.eq_dec phase 2 then SetTheory.implies left_value right_value else SetTheory.all right_value.
Lemma fields fs raw phase p q depth left_value : (phase = 2 \/ phase = 3) -> RenameFrames.entry fs raw (task phase p q depth left_value) ->
  exists root left_id, raw = (root,Z.of_nat depth,phase,left_id) /\ word root /\
    (exists parent, nth_error fs (Z.to_nat root) = Some parent) /\
    (phase = 2 -> word left_id /\ nth_error fs (Z.to_nat left_id) = Some left_value).
Proof.
  intros Hphase. destruct Hphase as [Hphase|Hphase]; subst phase;
    destruct raw as [[[root raw_depth] raw_phase] left_id]; cbn [task RenameFrames.entry].
  - intros [Hroot [Hdepth [-> [-> [Hparent [Hleft Hlookup]]]]]].
    exists root,left_id. split; [reflexivity|]. split; [exact Hroot|]. split; [eexists; exact Hparent|intros _; auto].
  - intros [Hroot [Hdepth [-> [-> Hparent]]]].
    exists root,left_id. split; [reflexivity|]. split; [exact Hroot|]. split; [eexists; exact Hparent|discriminate].
Qed.
Lemma arguments_spec phase fs left_id current left_value right_value : (phase = 2 \/ phase = 3) ->
  (phase = 2 -> word left_id /\ nth_error fs (Z.to_nat left_id) = Some left_value) ->
  word current -> nth_error fs (Z.to_nat current) = Some right_value ->
  FormulaEncoding.normal ((RenameJoin.arguments phase left_id current) vardef_0__intern_tag,
    (RenameJoin.arguments phase left_id current) vardef_0__intern_a,(RenameJoin.arguments phase left_id current) vardef_0__intern_b) /\
  FormulaEncoding.decode fs ((RenameJoin.arguments phase left_id current) vardef_0__intern_tag,
    (RenameJoin.arguments phase left_id current) vardef_0__intern_a,(RenameJoin.arguments phase left_id current) vardef_0__intern_b) =
    Some (joined phase left_value right_value).
Proof.
  intros Hphase Hleft Hcurrent Hlookup. destruct Hphase as [Hphase|Hphase]; subst phase.
  - destruct (Hleft eq_refl) as [Hleftword Hleftlookup].
    change (FormulaEncoding.normal (3,left_id,current) /\ FormulaEncoding.decode fs (3,left_id,current) = Some (SetTheory.implies left_value right_value)).
    split; [right; left; auto|]. unfold FormulaEncoding.decode. now rewrite Hleftlookup,Hlookup.
  - change (FormulaEncoding.normal (4,current,0) /\ FormulaEncoding.decode fs (4,current,0) = Some (SetTheory.all right_value)).
    split; [right; right; auto|]. change (option_map SetTheory.all (nth_error fs (Z.to_nat current)) = Some (SetTheory.all right_value)). now rewrite Hlookup.
Qed.
Theorem generated_join_refines (f : Frame) phase fs p q depth stack left_value right_value current observations :
  (phase = 2 \/ phase = 3) ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (length fs) <= 9223372036854775807 -> NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (task phase p q depth left_value :: stack) ->
  meta_value (machine f) 0 = current -> word current -> nth_error fs (Z.to_nat current) = Some right_value ->
  exists final next index, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0 = Z.of_nat index /\ nth_error next index = Some (joined phase left_value right_value) /\
    (exists extra, next = fs ++ extra) /\ meta_value (machine final) 8 = 0 /\ RenameConfiguration.preserved f final /\ (length next <= S (length fs))%nat.
Proof.
  intros Hphase Hmeta Herror Hcapacity Harena Hstack Hcurrent Hcurrentword Hlookup.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct (fields fs raw phase p q depth left_value Hphase Hentry) as [root [left_id [-> [Hroot [Hparent Hleft]]]]].
  destruct Hparent as [parent Hparent].
  assert (Hparentbound : (Z.to_nat root < length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnativebound : (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat).
  { pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  destruct (List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)) as [[tag a] b] eqn:Hformula.
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,phase,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  destruct (arguments_spec phase fs left_id current left_value right_value Hphase Hleft Hcurrentword Hlookup) as [Hnormal Hdecode].
  destruct (InternBounded.generated_refines (machine f) (fun _ => false) (RenameJoin.arguments phase left_id current)
    fs (joined phase left_value right_value) Harena Herror Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hflag [Hindex [Hindexword [Hnext [Hmeaning [extra Hextends]]]]]]]]]]].
  pose proof (InternGrowth.at_most_one (machine f) internstate _ _ fs next Harena Herror Hcapacity Hintern Hnext) as Hgrowth.
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (RenameJoin.arguments phase left_id current))
    (machine f,observations) = Some (tt,(internstate,observations)))
    by (apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]).
  assert (Hpostmeta : (10 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hlength. lia. }
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  exists (RenameJoin.result f internstate (length stack) root (Z.of_nat depth) phase left_id tag a b),next,index.
  split; [eapply RenameJoin.generated_join with (right_id := current); eassumption|]. split.
  - eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_meta; lia|exact Hnext].
  - split.
    + apply RenameFrames.pop with (task := task phase p q depth left_value); [exact Hpostmeta|].
      destruct Hframe as [Harrays [Hcells Hio]]. eapply RenameFrames.transport.
      * apply Hcells; lia.
      * apply Harrays; discriminate.
      * rewrite Hextends. now apply RenameFrames.extend.
    + split; [change (meta_value (store_meta internstate 10 (Z.of_nat (length stack))) 0 = Z.of_nat index); rewrite meta_store_other by lia; exact Hindex|]. split; [exact Hmeaning|]. split; [now exists extra|]. split.
      * change (meta_value (store_meta internstate 10 (Z.of_nat (length stack))) 8 = 0).
        rewrite meta_store_other by lia. exact Hflag.
      * split; [apply RenameConfiguration.join|exact Hgrowth].
Qed.
End RenameJoinRefinement.
