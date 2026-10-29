From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash ReadTwo ReadOne DecimalInput ReadNat ReadToken CommandInput TokenByte ClassEqualCommand ClassMemberCommand ClassEqualProtocol ClassMemberProtocol
 RenameMemoClassEqual RenameMemoClassMember RenameMemoParseDomain ClassMemberDomain RenameMemoResourceBounds FormulaTopology ClassLookup ClassStorage
 HistoryRefinement RenameStorage SemanticFrames FormulaEncoding Representation ArenaFrame FormulaProjection ReplyOK ReplyNO HashTable
 NativeState NativeProtocolLift NativeQueryCommands NativeCommandBoundary NativeClassBinaryCommands NativeStateFrames.
From NativeProof Require Import NativeClassBinaryBoundary SchemaEvaluationIndexCell SchemaEvaluationIndexBounds SchemaEvaluationIndexShiftClass SchemaEvaluationIndexClassEqual SchemaEvaluationIndexClassMember.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeClassAdvancedIndexInvariant.
Import IndexExecution SipHashExecution NativeClassBinaryBoundary.
Module Equal.
Import ClassEqualProtocol.
Theorem generated_control ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail index_bound observations :
  decimalBytes 7%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  RenameMemoClassEqual.ready s (Protocol.formulas logical) a b cls_a cls_b ->
  Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassEqual.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  Z.of_nat index_bound+2<=maximum ->
  exists final index fs, SchemaEvaluationIndexCell.bounded final fs (Protocol.classes logical) (index_bound+2) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs) /\ post RenameMemoClassEqual.work s logical final (Protocol.OK index) (logical_after logical fs) a b tail.
Proof.
  intros Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin [HrawInitial HclassBounds] HindexRoom.
  assert (Hmeta : (17<length (memory s arraydef_0__meta))%nat) by lia.
  assert (Hcode : Z.of_nat 7 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _=>false) (fun _=>0) 7 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical))
    by (exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena)).
  pose proof (argument_classes s logical ch chars a middle b last tail Hmeta Hclasses) as Harg_classes.
  pose proof (argument_history s logical ch chars a middle b last tail Hmeta Hhistory) as Harg_history.
  assert (Harg_wellformed : ClassLookup.wellformed arg).
  { apply (ClassLookup.transport s); [unfold arg; now rewrite ReadTwo.second_other by discriminate|exact Hwellformed]. }
  assert (Href_a : Z.of_nat a < meta_value arg 2) by (eapply reference; eassumption).
  assert (Href_b : Z.of_nat b < meta_value arg 2) by (eapply reference; eassumption).
  pose proof (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) as Harg_storage.
  assert (Hargmeta32 : (31<length (memory arg arraydef_0__meta))%nat) by (unfold arg; now rewrite ReadTwo.second_meta_length).
  assert (Hargsip : (0<length (memory arg arraydef_0__sipState))%nat) by (unfold arg; now rewrite ReadTwo.second_other by discriminate).
  assert (Hargtopology : FormulaTopology.ordered arg (length (Protocol.formulas logical)))
    by (eapply RenameMemoParseDomain.topology; eassumption).
  assert (Hargready : RenameMemoClassEqual.ready arg (Protocol.formulas logical) a b cls_a cls_b)
    by (eapply RenameMemoParseDomain.equal_ready; eassumption).
  assert (Hargbudget : Z.of_nat (length (Protocol.formulas logical)+RenameMemoClassEqual.work arg a b cls_a cls_b+0)<=RenameMemoResourceBounds.doubling_limit).
  { rewrite (RenameMemoParseDomain.equal_work s arg a b cls_a cls_b Harg_storage). now rewrite Nat.add_0_r. }
  destruct (SchemaEvaluationIndexClassEqual.generated_refines arg (fun _=>false) (ClassEqualCommand.arguments (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (Protocol.classes logical) a b cls_a cls_b 0 index_bound observations
    Hargmeta32 Hargsip Harg_arena Hargtopology Hfalse Hseconderror Harg_classes Harg_wellformed Hlookup_a Hlookup_b eq_refl eq_refl Hargready Hargbudget
     (SchemaEvaluationIndexBounds.raw_array_frame s arg (length (Protocol.formulas logical)) index_bound ltac:(unfold arg;apply ReadTwo.second_other;discriminate) HrawInitial)
     (SchemaEvaluationIndexCell.class_lookup index_bound (Protocol.classes logical) a cls_a HclassBounds Hlookup_a)
     (SchemaEvaluationIndexCell.class_lookup index_bound (Protocol.classes logical) b cls_b HclassBounds Hlookup_b) HindexRoom)
    as (built & fs & index & HrawBuilt & Hhelper & Hnext & Hindex & Hword & Hformula & Hprefix & Hflag & Hframe & Hbuilt_classes & Hbuilt_wellformed & Hreserve & Hbuilt_topology & Hgrowth).
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta : (17 < length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest]; lia).
  assert (Hpostbuffer : (20 <= length (memory built arraydef_0__printBuffer))%nat).
  { rewrite Harrays by (repeat split; discriminate). exact Hsecondbuffer. }
  pose proof (ClassEqualCommand.generated_command s bs ns _ _ arg built index (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    Href_a Href_b Hhelper Hpostmeta Hpostbuffer Hflag Hindex (proj2 Hword)) as Hrun.
  assert (Htail : stdin built = tail) by (rewrite Hinput_helper; exact Hinput).
  assert (Hstdout : stdout built = stdout s) by (rewrite Houtput_helper; exact Houtput).
  rewrite Htail,Hstdout in Hrun.
  exists (ReplyOKExecution.reply_state built index),index,fs. split.
  { split.
    - eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply ReplyOKExecution.reply_other;discriminate|exact HrawBuilt].
    - exact (SchemaEvaluationIndexShiftClass.classes_mono index_bound (index_bound+2) (Protocol.classes logical) ltac:(lia) HclassBounds). }
  split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup built)). split.
  - eapply Protocol.step_accept with (t:=logical_after logical fs).
    + eapply Protocol.accept_formula with (p:=VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)).
      * eapply Protocol.req_class_equal; eassumption.
      * split; [exact Hprefix|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - split; [exact (FormulaProjection.storage_arena built _ fs (FormulaProjection.reply_storage built index) Hnext)|].
    split;[now apply SemanticFrames.reply_classes|]. split.
    + apply SemanticFrames.reply_history. exact (RenameStorage.history_transport arg built logical Hframe Harg_history).
    + assert (HprefixIO:NativeQueryCommands.prefix s built tail).
      { unfold NativeQueryCommands.prefix. split;[exact Htail|]. split;[exact Hstdout|]. split;[congruence|].
        rewrite Hcells by (unfold RenameStorage.Cells.protected;lia).
        unfold arg. apply ReadTwo.second_meta_other;try exact Hmeta;lia. }
      unfold post. split.
      * exact (NativeQueryCommands.observed_boundary s bs ns (ReplyOKExecution.reply_state built index) observations _ (Protocol.OK index) tail
          Htoken Hbuffer Herror (NativeQueryCommands.ok_control s built index tail HprefixIO) Hrun).
      * split;[now apply reply_top|]. split;[now apply reply_good|]. split;[exact Hprefix|].
        split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
        unfold growth. rewrite Hlookup_a,Hlookup_b. cbn [logical_after Protocol.formulas].
        rewrite (RenameMemoParseDomain.equal_work s arg a b cls_a cls_b Harg_storage) in Hgrowth. exact Hgrowth.
Qed.
Theorem generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 7%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.class_at logical a = None \/ Protocol.class_at logical b = None) ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> ClassLookup.wellformed s ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  Z.of_nat index_bound+2<=maximum ->
  exists final, SchemaEvaluationIndexCell.bounded final (Protocol.formulas logical) (Protocol.classes logical) (index_bound+2) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ post RenameMemoClassEqual.work s logical final Protocol.NO logical a b tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin [HrawInitial HclassBounds] HindexRoom.
  assert (Hcode : Z.of_nat 7 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 7 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hbadrefs : meta_value arg 2 <= Z.of_nat a \/ meta_value arg 2 <= Z.of_nat b).
  { pose proof (proj1 Hclasses) as Hcount.
    assert (Hargcount : meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
    { unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount. }
    rewrite Hargcount. destruct Hbad as [Hbad|Hbad]; unfold Protocol.class_at in Hbad; apply nth_error_None in Hbad; lia. }
  pose proof (ClassEqualCommand.generated_rejected_command s bs ns _ _ arg (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hbadrefs) as Hrun.
  assert (Htail : stdin arg = tail) by exact Hinput.
  assert (Hstdout : stdout arg = stdout s) by exact Houtput.
  rewrite Htail, Hstdout in Hrun.
  exists (ReplyNOExecution.reply_state arg). split.
  { split.
    - eapply SchemaEvaluationIndexBounds.raw_arena_mono with (lower:=index_bound);[lia|].
      eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
      rewrite ReplyNOExecution.reply_memory. unfold arg. apply ReadTwo.second_other;discriminate.
    - exact (SchemaEvaluationIndexShiftClass.classes_mono index_bound (index_bound+2) (Protocol.classes logical) ltac:(lia) HclassBounds). }
  split; [exact Hrun|].
  split; [apply logical_rejected; [exact Hbad|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - exact (ArenaFrame.storage_arena arg _ (Protocol.formulas logical) (ArenaFrame.storage_output _ _) Harg_arena).
  - destruct Hclasses as [Hcount Hclassarray]. split.
    + split.
      * change (meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
        unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
      * change (Forall2 (fun entry cls => ClassStorage.decode (Protocol.formulas logical) entry = Some cls)
          (memory arg arraydef_0__classes) (Protocol.classes logical)).
        unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hclassarray.
    + split.
      * destruct Hhistory as [Hnumber Hprefix]. split.
        -- change (meta_value arg 3 = Z.of_nat (length (Protocol.history logical))).
           unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hnumber.
        -- change (firstn (length (Protocol.history logical)) (memory arg arraydef_0__theorems) = map Z.of_nat (Protocol.history logical)).
           unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hprefix.
      * unfold post. split.
        -- exact (NativeQueryCommands.observed_boundary s bs ns (ReplyNOExecution.reply_state arg) observations _ Protocol.NO tail
             Htoken Hbuffer Herror (NativeQueryCommands.no_control s arg tail (argument_prefix s ch chars a middle b last tail Hmeta)) Hrun).
        -- split.
           ++ apply (FormulaTopology.same s);[exact Htopology|]. intros parent Hparent.
              change (HashTableInvariant.tuple_at arg parent=HashTableInvariant.tuple_at s parent).
              unfold HashTableInvariant.tuple_at,arg. now rewrite ReadTwo.second_other by discriminate.
           ++ split.
              ** eapply ClassLookup.transport;[|exact Hwellformed].
                 change (memory arg arraydef_0__classes=memory s arraydef_0__classes).
                 unfold arg. apply ReadTwo.second_other;discriminate.
              ** split;[exists [];now rewrite app_nil_r|]. split;[reflexivity|]. split;[reflexivity|].
                 split;[reflexivity|]. split;[reflexivity|]. unfold growth.
                 destruct (Protocol.class_at logical a), (Protocol.class_at logical b);first [reflexivity|lia].
Qed.
Theorem generated_total_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 7%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassEqual.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassEqual.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  Z.of_nat index_bound+2<=maximum ->
  exists final reply next, SchemaEvaluationIndexCell.bounded final (Protocol.formulas next) (Protocol.classes next) (index_bound+2) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ post RenameMemoClassEqual.work s logical final reply next a b tail.
Proof.
  intros Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hdomain Ha Hb Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom.
  assert (Hmeta : (17<length (memory s arraydef_0__meta))%nat) by lia.
  destruct (Protocol.class_at logical a) as [cls_a|] eqn:Hlookup_a.
  - destruct (Protocol.class_at logical b) as [cls_b|] eqn:Hlookup_b.
    + destruct (Hdomain cls_a cls_b eq_refl eq_refl) as [Hready Hbudget].
      destruct (generated_control ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail index_bound observations
        Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom)
        as [final [index [fs Hpost]]]. exists final,(Protocol.OK index),(logical_after logical fs). exact Hpost.
    + destruct (generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_intror Hlookup_b) Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom) as [final Hpost].
      exists final,Protocol.NO,logical. exact Hpost.
  - destruct (generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_introl Hlookup_a) Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom) as [final Hpost].
    exists final,Protocol.NO,logical. exact Hpost.
Qed.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 7%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassEqual.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassEqual.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical -> ClassLookup.wellformed s ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  Z.of_nat index_bound+2<=maximum ->
  exists final reply next, SchemaEvaluationIndexCell.bounded final (Protocol.formulas next) (Protocol.classes next) (index_bound+2) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) reply next /\
    NativeState.represents final next /\ post RenameMemoClassEqual.work s logical final reply next a b tail /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb Hstate Hgood Hfirst Hmiddle Hlast Hinput Hbounded HindexRoom.
 destruct (generated_total_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
   Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate) Hgood
   (NativeState.history_representation _ _ Hstate) Hfirst Hmiddle Hlast Hinput Hbounded HindexRoom)
 as (final & reply & next & HnextBounded & Hrun & Hstep & Harena & Hclasses & Hhistory & Hpost).
 exists final,reply,next. split;[exact HnextBounded|]. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 7 ch chars s bs ns first_separator
    (decimalBytes a++middle::decimalBytes b++last::tail) observations final _ logical (Protocol.Req 7 [a;b] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact Hpost|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Equal.
Module Member.
Import ClassMemberProtocol.
Theorem generated_control ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail index_bound observations :
  decimalBytes 8%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  RenameMemoClassMember.ready s (Protocol.formulas logical) a b cls_a cls_b ->
  Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassMember.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  2*Z.of_nat index_bound+3<=maximum ->
  exists final index fs, SchemaEvaluationIndexCell.bounded final fs (Protocol.classes logical) (2*index_bound+3) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 8 [a;b] []) (Protocol.OK index) (logical_after logical fs) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs) /\ post RenameMemoClassMember.work s logical final (Protocol.OK index) (logical_after logical fs) a b tail.
Proof.
  intros Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin [HrawInitial HclassBounds] HindexRoom.
  assert (Hmeta : (17<length (memory s arraydef_0__meta))%nat) by lia.
  assert (Hcode : Z.of_nat 8 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _=>false) (fun _=>0) 8 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical))
    by (exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena)).
  pose proof (argument_classes s logical ch chars a middle b last tail Hmeta Hclasses) as Harg_classes.
  pose proof (argument_history s logical ch chars a middle b last tail Hmeta Hhistory) as Harg_history.
  assert (Harg_wellformed : ClassLookup.wellformed arg).
  { apply (ClassLookup.transport s); [unfold arg; now rewrite ReadTwo.second_other by discriminate|exact Hwellformed]. }
  assert (Href_a : Z.of_nat a < meta_value arg 2) by (eapply reference; eassumption).
  assert (Href_b : Z.of_nat b < meta_value arg 2) by (eapply reference; eassumption).
  pose proof (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) as Harg_storage.
  assert (Hargmeta32 : (31<length (memory arg arraydef_0__meta))%nat) by (unfold arg; now rewrite ReadTwo.second_meta_length).
  assert (Hargsip : (0<length (memory arg arraydef_0__sipState))%nat) by (unfold arg; now rewrite ReadTwo.second_other by discriminate).
  assert (Hargtopology : FormulaTopology.ordered arg (length (Protocol.formulas logical)))
    by (eapply RenameMemoParseDomain.topology; eassumption).
  assert (Hargready : RenameMemoClassMember.ready arg (Protocol.formulas logical) a b cls_a cls_b)
    by (eapply ClassMemberDomain.member_ready; eassumption).
  assert (Hargbudget : Z.of_nat (length (Protocol.formulas logical)+RenameMemoClassMember.work arg a b cls_a cls_b+0)<=RenameMemoResourceBounds.doubling_limit).
  { rewrite (ClassMemberDomain.member_work s arg a b cls_a cls_b Harg_storage). now rewrite Nat.add_0_r. }
  destruct (SchemaEvaluationIndexClassMember.generated_refines arg (fun _=>false) (ClassMemberCommand.arguments (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (Protocol.classes logical) a b cls_a cls_b 0 index_bound observations
    Hargmeta32 Hargsip Harg_arena Hargtopology Hfalse Hseconderror Harg_classes Harg_wellformed Hlookup_a Hlookup_b eq_refl eq_refl Hargready Hargbudget
     (SchemaEvaluationIndexBounds.raw_array_frame s arg (length (Protocol.formulas logical)) index_bound ltac:(unfold arg;apply ReadTwo.second_other;discriminate) HrawInitial)
     (SchemaEvaluationIndexCell.class_lookup index_bound (Protocol.classes logical) a cls_a HclassBounds Hlookup_a)
     (SchemaEvaluationIndexCell.class_lookup index_bound (Protocol.classes logical) b cls_b HclassBounds Hlookup_b) HindexRoom)
    as (built & fs & index & HrawBuilt & Hhelper & Hnext & Hindex & Hword & Hformula & Hprefix & Hflag & Hframe & Hbuilt_classes & Hbuilt_wellformed & Hreserve & Hbuilt_topology & Hgrowth).
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta : (17 < length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest]; lia).
  assert (Hpostbuffer : (20 <= length (memory built arraydef_0__printBuffer))%nat).
  { rewrite Harrays by (repeat split; discriminate). exact Hsecondbuffer. }
  pose proof (ClassMemberCommand.generated_command s bs ns _ _ arg built index (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    Href_a Href_b Hhelper Hpostmeta Hpostbuffer Hflag Hindex (proj2 Hword)) as Hrun.
  assert (Htail : stdin built = tail) by (rewrite Hinput_helper; exact Hinput).
  assert (Hstdout : stdout built = stdout s) by (rewrite Houtput_helper; exact Houtput).
  rewrite Htail,Hstdout in Hrun.
  exists (ReplyOKExecution.reply_state built index),index,fs. split.
  { split.
    - eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply ReplyOKExecution.reply_other;discriminate|exact HrawBuilt].
    - exact (SchemaEvaluationIndexShiftClass.classes_mono index_bound (2*index_bound+3) (Protocol.classes logical) ltac:(lia) HclassBounds). }
  split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup built)). split.
  - eapply Protocol.step_accept with (t:=logical_after logical fs).
    + eapply Protocol.accept_formula with (p:=VirtualClasses.erase (VirtualClasses.class_member cls_a cls_b)).
      * eapply Protocol.req_class_member; eassumption.
      * split; [exact Hprefix|]. split; [exact Hunique|]. split; [exact Hformula|]. exists []; now rewrite app_nil_r.
    + apply HistoryRefinement.retained_refl. exact Hunique.
  - split; [exact (FormulaProjection.storage_arena built _ fs (FormulaProjection.reply_storage built index) Hnext)|].
    split;[now apply SemanticFrames.reply_classes|]. split.
    + apply SemanticFrames.reply_history. exact (RenameStorage.history_transport arg built logical Hframe Harg_history).
    + assert (HprefixIO:NativeQueryCommands.prefix s built tail).
      { unfold NativeQueryCommands.prefix. split;[exact Htail|]. split;[exact Hstdout|]. split;[congruence|].
        rewrite Hcells by (unfold RenameStorage.Cells.protected;lia).
        unfold arg. apply ReadTwo.second_meta_other;try exact Hmeta;lia. }
      unfold post. split.
      * exact (NativeQueryCommands.observed_boundary s bs ns (ReplyOKExecution.reply_state built index) observations _ (Protocol.OK index) tail
          Htoken Hbuffer Herror (NativeQueryCommands.ok_control s built index tail HprefixIO) Hrun).
      * split;[now apply reply_top|]. split;[now apply reply_good|]. split;[exact Hprefix|].
        split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|].
        unfold growth. rewrite Hlookup_a,Hlookup_b. cbn [logical_after Protocol.formulas].
        rewrite (ClassMemberDomain.member_work s arg a b cls_a cls_b Harg_storage) in Hgrowth. exact Hgrowth.
Qed.
Theorem generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 8%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.class_at logical a = None \/ Protocol.class_at logical b = None) ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> ClassLookup.wellformed s ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  2*Z.of_nat index_bound+3<=maximum ->
  exists final, SchemaEvaluationIndexCell.bounded final (Protocol.formulas logical) (Protocol.classes logical) (2*index_bound+3) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 8 [a;b] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\ post RenameMemoClassMember.work s logical final Protocol.NO logical a b tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin [HrawInitial HclassBounds] HindexRoom.
  assert (Hcode : Z.of_nat 8 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 8 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hbadrefs : meta_value arg 2 <= Z.of_nat a \/ meta_value arg 2 <= Z.of_nat b).
  { pose proof (proj1 Hclasses) as Hcount.
    assert (Hargcount : meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
    { unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount. }
    rewrite Hargcount. destruct Hbad as [Hbad|Hbad]; unfold Protocol.class_at in Hbad; apply nth_error_None in Hbad; lia. }
  pose proof (ClassMemberCommand.generated_rejected_command s bs ns _ _ arg (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hbadrefs) as Hrun.
  assert (Htail : stdin arg = tail) by exact Hinput.
  assert (Hstdout : stdout arg = stdout s) by exact Houtput.
  rewrite Htail, Hstdout in Hrun.
  exists (ReplyNOExecution.reply_state arg). split.
  { split.
    - eapply SchemaEvaluationIndexBounds.raw_arena_mono with (lower:=index_bound);[lia|].
      eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
      rewrite ReplyNOExecution.reply_memory. unfold arg. apply ReadTwo.second_other;discriminate.
    - exact (SchemaEvaluationIndexShiftClass.classes_mono index_bound (2*index_bound+3) (Protocol.classes logical) ltac:(lia) HclassBounds). }
  split; [exact Hrun|].
  split; [apply logical_rejected; [exact Hbad|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - exact (ArenaFrame.storage_arena arg _ (Protocol.formulas logical) (ArenaFrame.storage_output _ _) Harg_arena).
  - destruct Hclasses as [Hcount Hclassarray]. split.
    + split.
      * change (meta_value arg 2 = Z.of_nat (length (Protocol.classes logical))).
        unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hcount.
      * change (Forall2 (fun entry cls => ClassStorage.decode (Protocol.formulas logical) entry = Some cls)
          (memory arg arraydef_0__classes) (Protocol.classes logical)).
        unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hclassarray.
    + split.
      * destruct Hhistory as [Hnumber Hprefix]. split.
        -- change (meta_value arg 3 = Z.of_nat (length (Protocol.history logical))).
           unfold arg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Hnumber.
        -- change (firstn (length (Protocol.history logical)) (memory arg arraydef_0__theorems) = map Z.of_nat (Protocol.history logical)).
           unfold arg. rewrite ReadTwo.second_other by discriminate. exact Hprefix.
      * unfold post. split.
        -- exact (NativeQueryCommands.observed_boundary s bs ns (ReplyNOExecution.reply_state arg) observations _ Protocol.NO tail
             Htoken Hbuffer Herror (NativeQueryCommands.no_control s arg tail (argument_prefix s ch chars a middle b last tail Hmeta)) Hrun).
        -- split.
           ++ apply (FormulaTopology.same s);[exact Htopology|]. intros parent Hparent.
              change (HashTableInvariant.tuple_at arg parent=HashTableInvariant.tuple_at s parent).
              unfold HashTableInvariant.tuple_at,arg. now rewrite ReadTwo.second_other by discriminate.
           ++ split.
              ** eapply ClassLookup.transport;[|exact Hwellformed].
                 change (memory arg arraydef_0__classes=memory s arraydef_0__classes).
                 unfold arg. apply ReadTwo.second_other;discriminate.
              ** split;[exists [];now rewrite app_nil_r|]. split;[reflexivity|]. split;[reflexivity|].
                 split;[reflexivity|]. split;[reflexivity|]. unfold growth.
                 destruct (Protocol.class_at logical a), (Protocol.class_at logical b);first [reflexivity|lia].
Qed.
Theorem generated_total_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 8%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassMember.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassMember.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  2*Z.of_nat index_bound+3<=maximum ->
  exists final reply next, SchemaEvaluationIndexCell.bounded final (Protocol.formulas next) (Protocol.classes next) (2*index_bound+3) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 8 [a;b] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ post RenameMemoClassMember.work s logical final reply next a b tail.
Proof.
  intros Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hdomain Ha Hb Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom.
  assert (Hmeta : (17<length (memory s arraydef_0__meta))%nat) by lia.
  destruct (Protocol.class_at logical a) as [cls_a|] eqn:Hlookup_a.
  - destruct (Protocol.class_at logical b) as [cls_b|] eqn:Hlookup_b.
    + destruct (Hdomain cls_a cls_b eq_refl eq_refl) as [Hready Hbudget].
      destruct (generated_control ch chars s logical bs ns a b cls_a cls_b first_separator middle last tail index_bound observations
        Hencoding Hmeta32 Hsip Htopology Htoken Hbuffer Hpending Herror Hfalse Hready Hbudget Ha Hb Hlookup_a Hlookup_b Harena Hclasses Hwellformed Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom)
        as [final [index [fs Hpost]]]. exists final,(Protocol.OK index),(logical_after logical fs). exact Hpost.
    + destruct (generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
        Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_intror Hlookup_b) Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom) as [final Hpost].
      exists final,Protocol.NO,logical. exact Hpost.
  - destruct (generated_rejected_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb (or_introl Hlookup_a) Htopology Hwellformed Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hin Hbounded HindexRoom) as [final Hpost].
    exists final,Protocol.NO,logical. exact Hpost.
Qed.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail index_bound observations :
  decimalBytes 8%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassMember.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassMember.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical -> ClassLookup.wellformed s ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
  2*Z.of_nat index_bound+3<=maximum ->
  exists final reply next, SchemaEvaluationIndexCell.bounded final (Protocol.formulas next) (Protocol.classes next) (2*index_bound+3) /\
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 8 [a;b] []) reply next /\
    NativeState.represents final next /\ post RenameMemoClassMember.work s logical final reply next a b tail /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb Hstate Hgood Hfirst Hmiddle Hlast Hinput Hbounded HindexRoom.
 destruct (generated_total_control ch chars s logical bs ns a b first_separator middle last tail index_bound observations
   Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate) Hgood
   (NativeState.history_representation _ _ Hstate) Hfirst Hmiddle Hlast Hinput Hbounded HindexRoom)
 as (final & reply & next & HnextBounded & Hrun & Hstep & Harena & Hclasses & Hhistory & Hpost).
 exists final,reply,next. split;[exact HnextBounded|]. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 8 ch chars s bs ns first_separator
    (decimalBytes a++middle::decimalBytes b++last::tail) observations final _ logical (Protocol.Req 8 [a;b] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact Hpost|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Member.
End NativeClassAdvancedIndexInvariant.
