From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift LocalParameters IndexFrame Intern InternBounded InternGrowth Observation ObservedLocal RenameStack RenameFrames RenameStructure RenameAtom FormulaEncoding Representation HashTable ArenaFrame RenameConfiguration.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameAtomRefinement.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameStructure.
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
Theorem generated_atom_refines (f : Frame) tag fs i j depth stack m shift arg observations :
  (tag = 1 \/ tag = 2) ->
  nums f vardef_0__rename_mode = mode_number m -> nums f vardef_0__rename_shift = Z.of_nat shift -> nums f vardef_0__rename_arg = Z.of_nat arg ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (length fs) <= 9223372036854775807 -> NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (atom tag i j) depth :: stack) ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) j)) ->
  exists final next index, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0 = Z.of_nat index /\
    nth_error next index = Some (SetTheory.rename (under_binders depth (renaming m shift arg)) (atom tag i j)) /\
    (exists extra, next = fs ++ extra) /\ meta_value (machine final) 8 = 0 /\ RenameConfiguration.preserved f final /\ (length next <= S (length fs))%nat.
Proof.
  intros Htag Hmode Hshift Harg Hmeta Herror Hcapacity Harena Hstack Hi Hj Hshiftword Hargword Hmapped_i Hmapped_j.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]; subst raw_depth phase.
  assert (Hsourcebound : (Z.to_nat root < length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnativebound : (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat).
  { pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  assert (Hformula : List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (tag,Z.of_nat i,Z.of_nat j)).
  { apply (FormulaEncoding.decode_injective fs _ _ (atom tag i j) (proj1 (proj2 (proj2 Harena)))).
    - exact (proj2 (proj2 (proj2 Harena)) _ Hsourcebound).
    - now apply normal.
    - exact (NativeRepresentation.represented_lookup _ _ _ _ (proj1 (proj2 Harena)) Hlookup).
    - now apply decoded. }
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,0,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  set (first := IndexFrame.result_state (machine f) m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (second := IndexFrame.result_state first m (Z.of_nat j) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (mapped_i := under_binders depth (renaming m shift arg) i).
  set (mapped_j := under_binders depth (renaming m shift arg) j).
  assert (Hfirst : execObserved (funcdef_0__renameIndex (fun _ => false)
      (IndexFrame.native_arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
      (machine f,observations) = Some (tt,(first,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hfirstmeta : (10 < length (memory first arraydef_0__meta))%nat) by (unfold first; now rewrite IndexFrame.result_meta_length).
  assert (Hfirstvalue : meta_value first 0 = Z.of_nat mapped_i).
  { unfold first,mapped_i. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecond : execObserved (funcdef_0__renameIndex (fun _ => false)
      (IndexFrame.native_arguments (Z.of_nat j) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
      (first,observations) = Some (tt,(second,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hsecondmeta : (10 < length (memory second arraydef_0__meta))%nat) by (unfold second; now rewrite IndexFrame.result_meta_length).
  assert (Hsecondvalue : meta_value second 0 = Z.of_nat mapped_j).
  { unfold second,mapped_j. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecondclear : meta_value second 8 = 0).
  { unfold second,first. rewrite !IndexFrame.result_meta_other by lia. exact Herror. }
  assert (Hsecondarena : NativeRepresentation.canonical_arena second fs)
    by (apply IndexFrame.result_arena; now apply IndexFrame.result_arena).
  assert (Hsecondframes : RenameFrames.represents second fs (RenameStack.visit (atom tag i j) depth :: stack))
    by (apply IndexFrame.result_frames; now apply IndexFrame.result_frames).
  assert (Hnormal : FormulaEncoding.normal (tag,Z.of_nat mapped_i,Z.of_nat mapped_j)) by now apply normal.
  pose proof (decoded fs tag mapped_i mapped_j Htag) as Hdecode.
  destruct (InternBounded.generated_refines second (fun _ => false) (RenameAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j))
    fs (atom tag mapped_i mapped_j) Hsecondarena Hsecondclear Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hflag [Hindex [Hindexword [Hnext [Hmeaning [extra Hextends]]]]]]]]]]].
  pose proof (InternGrowth.at_most_one second internstate _ _ fs next Hsecondarena Hsecondclear Hcapacity Hintern Hnext) as Hgrowth.
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (RenameAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)))
    (second,observations) = Some (tt,(internstate,observations)))
    by (apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]).
  assert (Hpostmeta : (10 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hlength. lia. }
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  exists (RenameAtom.result f internstate (length stack) root (Z.of_nat depth) left_id tag (Z.of_nat i) (Z.of_nat j) (Z.of_nat mapped_i) (Z.of_nat mapped_j)),next,index.
  split.
  - eapply RenameAtom.generated_atom with (first := first) (second := second) (mode := mode_number m)
      (shift := Z.of_nat shift) (arg := Z.of_nat arg); eassumption.
  - split; [eapply ArenaFrame.storage_arena; [apply ArenaFrame.storage_meta; lia|exact Hnext]|]. split.
    + apply RenameFrames.pop with (task := RenameStack.visit (atom tag i j) depth); [exact Hpostmeta|].
      destruct Hframe as [Harrays [Hcells Hio]]. eapply RenameFrames.transport.
      * apply Hcells; lia.
      * apply Harrays; discriminate.
      * rewrite Hextends. now apply RenameFrames.extend.
    + split.
      * change (meta_value (store_meta internstate 10 (Z.of_nat (length stack))) 0 = Z.of_nat index).
        rewrite meta_store_other by lia. exact Hindex.
      * split; [rewrite renamed_atom by exact Htag; exact Hmeaning|]. split; [now exists extra|]. split.
        -- change (meta_value (store_meta internstate 10 (Z.of_nat (length stack))) 8 = 0).
           rewrite meta_store_other by lia. exact Hflag.
        -- split; [apply RenameConfiguration.atom|exact Hgrowth].
Qed.
End RenameAtomRefinement.
