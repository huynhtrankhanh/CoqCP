From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash RenameMemoEventSchedule RenameStorage
  ClassStorage HistoryRefinement NameRepresentation SchemaMetadata InternalIO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.
Module RenameMemoOutput.
Import IndexExecution SipHashExecution.
(* Pointwise preservation of every occupied source index is an actual list
   prefix, rather than merely agreement on a selected set of reachable nodes. *)
Theorem prefix_list {A : Type} (xs ys : list A) :
  (forall index value, nth_error xs index=Some value -> nth_error ys index=Some value) ->
  exists extra, ys=xs++extra.
Proof.
  induction xs as [|head tail IH] in ys |- *.
  - intro Hprefix. exists ys. reflexivity.
  - intro Hprefix. destruct ys as [|other rest].
    + specialize (Hprefix 0 head eq_refl). discriminate.
    + assert (Hhead : other=head).
      { specialize (Hprefix 0 head eq_refl). cbn in Hprefix. now injection Hprefix. }
      subst other. destruct (IH rest) as [extra Hextra].
      * intros index value Hlookup. exact (Hprefix (S index) value Hlookup).
      * exists extra. cbn. now rewrite Hextra.
Qed.
Theorem source_extension xs ys : RenameMemoEventSchedule.source_prefix xs ys -> exists extra,ys=xs++extra.
Proof. apply prefix_list. Qed.
Theorem exported s bs ns final observations after fs next :
  execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(final,after)) ->
  RenameMemoEventSchedule.source_prefix fs next ->
  (exists extra,next=fs++extra) /\ RenameStorage.logical_frame s final.
Proof.
  intros Hrun Hprefix. split; [now apply source_extension|]. eapply RenameStorage.rename_frame; exact Hrun.
Qed.
(* Registry preservation is stated over represented mathematical objects. In
   particular, old virtual classes retain their meanings in the extended arena. *)
Definition registries s fs classes logical bindings expressions :=
  ClassStorage.represents s fs classes /\ HistoryRefinement.represents s logical /\
  NameRepresentation.represents s bindings /\ SchemaMetadata.represents s expressions.
Theorem transport s t fs next classes logical bindings expressions :
  RenameStorage.logical_frame s t -> RenameMemoEventSchedule.source_prefix fs next ->
  registries s fs classes logical bindings expressions -> registries t next classes logical bindings expressions.
Proof.
  intros Hframe Hprefix [Hclasses [Hhistory [Hnames Hschemas]]].
  destruct (source_extension fs next Hprefix) as [extra ->]. unfold registries.
  split; [eapply RenameStorage.classes_transport; eassumption|].
  split; [eapply RenameStorage.history_transport; eassumption|].
  split; [eapply RenameStorage.names_transport; eassumption|].
  eapply RenameStorage.schemas_transport; eassumption.
Qed.
Theorem executed s bs ns final observations after fs next classes logical bindings expressions :
  execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(final,after)) ->
  RenameMemoEventSchedule.source_prefix fs next -> registries s fs classes logical bindings expressions ->
  registries final next classes logical bindings expressions /\
  stdin final=stdin s /\ stdout final=stdout s.
Proof.
  intros Hrun Hprefix Hregistries.
  pose proof (RenameStorage.rename_frame s bs ns final observations after Hrun) as Hframe.
  split; [eapply transport; eassumption|]. exact (proj2 (proj2 Hframe)).
Qed.
End RenameMemoOutput.
