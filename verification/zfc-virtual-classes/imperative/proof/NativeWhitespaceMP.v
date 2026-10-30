From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash HashTable ObservedLocal ReadTwo TokenByte FormulaEncoding Representation ArenaFrame ClassStorage HistoryRefinement SemanticFrames HistoryLookup LogicalHistory ModusPonens NativeWhitespaceMPRefinement CommandMP CommandMPReject ReplyNO.
From NativeProof Require Import NativeArgumentReadsTwoFull NativeState NativeStateFrames NativeProtocolLift.
From Trusted Require Import Guarantees.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceMP.
Import IndexExecution SipHashExecution HashTableInvariant ObservedLocal NativeWhitespaceMPRefinement.
Theorem generated_rejected_helper s bs ns i j node antecedent tag left right observations :
  (8 < length (memory s arraydef_0__meta))%nat ->
  (i < length (memory s arraydef_0__theorems))%nat -> (j < length (memory s arraydef_0__theorems))%nat ->
  (node < length (memory s arraydef_0__formulas))%nat ->
  List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat node ->
  List.nth j (memory s arraydef_0__theorems) 0 = antecedent -> tuple_at s node = (tag,left,right) ->
  (tag <> 3 \/ left <> antecedent) ->
  ns vardef_0__modusPonens_implication = Z.of_nat i -> ns vardef_0__modusPonens_antecedent = Z.of_nat j ->
  execObserved (funcdef_0__modusPonens bs ns) (s,observations) = Some (tt,(ReplyNOExecution.reply_state s,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin s|}])).
Proof.
  intros Hmeta Hi Hj Hnode Hlookupi Hlookupj Htuple Hbad Hni Hnj.
  unfold funcdef_0__modusPonens. rewrite ObservedLocal.eliminate_correct.
  pose proof (ModusPonensExecution.generated_rejected_body {|machine := s; bools := bs; nums := ns|}
    i j node antecedent tag left right observations Hmeta Hi Hj Hnode Hlookupi Hlookupj Htuple Hbad Hni Hnj) as Hrun.
  unfold ModusPonensExecution.Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Lemma logical_rejected logical i j :
  (forall p q, ~ (Protocol.theorem_at logical i = Some (SetTheory.implies p q) /\ Protocol.theorem_at logical j = Some p)) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 12 [i;j] []) Protocol.NO logical.
Proof.
  intros Hbad Hunique. apply Protocol.step_reject; [|now apply HistoryRefinement.retained_refl].
  intros r t Haccept. inversion Haccept; subst;
    first [match goal with H : Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H : Protocol.proof_request _ _ _ |- _ => inversion H; subst; eapply Hbad; split; eassumption end].
Qed.
Lemma invalid_rejected logical i j :
  (nth_error (Protocol.history logical) i = None \/ nth_error (Protocol.history logical) j = None) ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 12 [i;j] []) Protocol.NO logical.
Proof.
  intros Hbad Hunique. apply logical_rejected; [|exact Hunique]. intros p q [Hi Hj].
  unfold Protocol.theorem_at in Hi,Hj. destruct Hbad as [Hbad|Hbad]; rewrite Hbad in *; discriminate.
Qed.
Lemma guard_rejected s logical i j node antecedent tag left right :
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) -> HistoryRefinement.represents s logical ->
  List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat node ->
  List.nth j (memory s arraydef_0__theorems) 0 = antecedent -> tuple_at s node = (tag,left,right) ->
  (tag <> 3 \/ left <> antecedent) -> Protocol.step logical (Protocol.Req 12 [i;j] []) Protocol.NO logical.
Proof.
  intros Harena Hhistory Hni Hnj Htuple Hbad. apply logical_rejected; [|now apply (SemanticFrames.arena_NoDup s)].
  intros p q [Hi Hj]. destruct (HistoryLookup.modus_ponens_nodes s logical i j p q Harena Hhistory Hi Hj)
    as [node' [aid [bid [Hbi [Hbj [Hnode [Hni' [Hnj' [Htuple' Hlookup]]]]]]]]].
  assert (Hnodeeq : node = node') by (rewrite Hni in Hni'; lia).
  subst node'. rewrite Htuple in Htuple'. injection Htuple' as Htag Hleft Hright.
  destruct Hbad as [Hbad|Hbad]; congruence.
Qed.
Theorem generated_invalid_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  (nth_error (Protocol.history logical) i = None \/ nth_error (Protocol.history logical) j = None) ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbad Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  assert (Hopword : Z.of_nat 12 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 12 49 [50] i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat i \/ meta_value arg 3 <= Z.of_nat j).
  { rewrite (proj1 Harg_history). destruct Hbad as [Hbad|Hbad]; apply nth_error_None in Hbad; [left|right]; lia. }
  pose proof (CommandMPReject.generated_command s bs ns _ _ arg (Z.of_nat i) (Z.of_nat j) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply invalid_rejected; [exact Hbad|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harena]. eapply ArenaFrame.storage_trans;
      [exact (ReadTwo.second_storage s 49 [50] i middle_separator j last_separator tail Hmeta)|apply ArenaFrame.storage_output].
  - split; [now apply argument_classes|exact Harg_history].
Qed.
Theorem generated_guard_protocol s logical bs ns i j node aid tag left right first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  nth_error (Protocol.history logical) i = Some node -> nth_error (Protocol.history logical) j = Some aid ->
  tuple_at s node = (tag,left,right) -> (tag <> 3 \/ left <> Z.of_nat aid) -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hlookupi Hlookupj Htuple Hbad Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  assert (Hopword : Z.of_nat 12 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 12 49 [50] i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (meta_value arg 8 = 0) in Hargerror.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s 49 [50] i middle_separator j last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  destruct (HistoryLookup.native_lookup arg logical i node Harg_history Hlookupi) as [Hbi Hni].
  destruct (HistoryLookup.native_lookup arg logical j aid Harg_history Hlookupj) as [Hbj Hnj].
  destruct (Hvalid i node Hlookupi) as [p Hp].
  pose proof (proj1 (HistoryLookup.formula_reference arg _ node p Harg_arena Hp)) as Hnode.
  assert (Htuplearg : tuple_at arg node = (tag,left,right)).
  { unfold tuple_at, arg, argument_state. rewrite ReadTwo.second_other by discriminate. exact Htuple. }
  assert (Hiref : Z.of_nat i < meta_value arg 3).
  { rewrite (proj1 Harg_history). assert (i < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hjref : Z.of_nat j < meta_value arg 3).
  { rewrite (proj1 Harg_history). assert (j < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  pose proof (generated_rejected_helper arg (fun _ => false) (CommandMPExecution.arguments (Z.of_nat i) (Z.of_nat j))
    i j node (Z.of_nat aid) tag left right observations ltac:(lia) Hbi Hbj Hnode Hni Hnj Htuplearg Hbad eq_refl eq_refl) as Hmp.
  pose proof (CommandMPExecution.generated_command s bs ns _ _ arg (ReplyNOExecution.reply_state arg) (Z.of_nat i) (Z.of_nat j) observations _
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hargmeta Hargnumber Hargvalid Hargerror
    Hiref Hjref Hmp ltac:(change (8 < length (memory arg arraydef_0__meta))%nat; lia) Hargerror) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [exact (guard_rejected arg logical i j node (Z.of_nat aid) tag left right Harg_arena Harg_history Hni Hnj Htuplearg Hbad)|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harg_arena]. apply ArenaFrame.storage_output.
  - split; [now apply argument_classes|exact Harg_history].
Qed.
Theorem generated_total_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) reply next /\
    NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ LogicalHistory.valid next.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  destruct (nth_error (Protocol.history logical) i) as [node|] eqn:Hlookupi.
  - destruct (nth_error (Protocol.history logical) j) as [aid|] eqn:Hlookupj.
    + destruct (tuple_at s node) as [[tag left] right] eqn:Htuple.
      destruct (Z.eq_dec tag 3) as [Htag|Htag].
      * destruct (Z.eq_dec left (Z.of_nat aid)) as [Hleft|Hleft].
        -- subst tag left. destruct (Hvalid i node Hlookupi) as [pnode Hpnode].
           destruct (Hvalid j aid Hlookupj) as [pante Hpante].
           destruct (HistoryLookup.formula_reference s _ node pnode Harena Hpnode) as [_ [_ [_ Hdecode]]].
           rewrite Htuple in Hdecode.
           change (match nth_error (Protocol.formulas logical) (Z.to_nat (Z.of_nat aid)),
             nth_error (Protocol.formulas logical) (Z.to_nat right) with
             | Some p,Some q => Some (SetTheory.implies p q) | _,_ => None end = Some pnode) in Hdecode.
           unfold Protocol.formula_at in Hpante. rewrite Nat2Z.id, Hpante in Hdecode.
           destruct (nth_error (Protocol.formulas logical) (Z.to_nat right)) as [q|] eqn:Hq; [|discriminate].
           injection Hdecode as <-.
           assert (Himp : Protocol.theorem_at logical i = Some (SetTheory.implies pante q)).
           { unfold Protocol.theorem_at. rewrite Hlookupi. exact Hpnode. }
           assert (Hante : Protocol.theorem_at logical j = Some pante).
           { unfold Protocol.theorem_at. rewrite Hlookupj. exact Hpante. }
           destruct (NativeWhitespaceMPRefinement.generated_protocol s logical bs ns i j pante q first_separator prefix1 middle_separator prefix2 last_separator tail observations
             Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Himp Hante Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
             as [final [fid [Hrun [Hstep [Hfid [Hnextarena [Hnextclasses Hnexthistory]]]]]]].
           exists final,(Protocol.OK (length (Protocol.history logical))),(Protocol.with_history logical (Protocol.history logical ++ [fid])).
           split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Hnextarena|]. split; [exact Hnextclasses|].
           split; [exact Hnexthistory|]. eapply LogicalHistory.step_valid; eassumption.
        -- destruct (generated_guard_protocol s logical bs ns i j node aid tag left right first_separator prefix1 middle_separator prefix2 last_separator tail observations
             Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hlookupi Hlookupj Htuple (or_intror Hleft) Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
             as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
           exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
      * destruct (generated_guard_protocol s logical bs ns i j node aid tag left right first_separator prefix1 middle_separator prefix2 last_separator tail observations
          Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hlookupi Hlookupj Htuple (or_introl Htag) Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
          as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
        exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
    + destruct (generated_invalid_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
        Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword (or_intror Hlookupj) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
        as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
      exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
  - destruct (generated_invalid_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword (or_introl Hlookupi) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
      as [final [Hrun [Hstep [Ha [Hc Hh]]]]].
    exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split; [exact Hc|]. split; assumption.
Qed.
Theorem generated_total_state s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat i <= maximum -> Z.of_nat j <= maximum -> Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical -> TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator ->
  TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) reply next /\ NativeState.represents final next /\
    LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Hstate Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
 destruct(generated_total_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid (NativeState.formula_representation _ _ Hstate)
   (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
 as(final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hvalid').
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 12 49 [50] s bs ns first_separator
    (prefix1++decimalBytes i++middle_separator::prefix2++decimalBytes j++last_separator::tail) observations final _ logical (Protocol.Req 12 [i;j] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact Hvalid'|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End NativeWhitespaceMP.
