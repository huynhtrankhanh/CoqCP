From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash HashTable ObservedLocal NativeState NativeStateFrames NativeProtocolLift NativeTheoremBoundary
 ReadOne ReadTwo ParsedState TokenByte FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage HistoryRefinement
 HistoryLookup HistoryStorage LogicalHistory SemanticFrames CommandRestate CommandRestateReject RestateRefinement
 ModusPonens ModusPonensRefinement ModusPonensRejection CommandMP CommandMPReject ReplyOK ReplyNO SchemaProtocolFrame NativeArgumentReadsTwoFull.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceMPBoundary.
Import IndexExecution SipHashExecution HashTableInvariant ObservedLocal NativeTheoremBoundary.
Lemma zero_formula_growth before request reply after : Protocol.step before request reply after ->
 (length (Protocol.formulas after)<=length (Protocol.formulas before))%nat -> Protocol.formulas after=Protocol.formulas before.
Proof.
 intros Hstep Hlength. destruct (SchemaProtocolFrame.step_prefixes _ _ _ _ Hstep) as [[extra Hextra] Hrest].
 rewrite Hextra,length_app in Hlength. assert (extra=[]) by (destruct extra;[reflexivity|cbn [length] in Hlength;lia]).
 subst extra. now rewrite Hextra,app_nil_r.
Qed.
Module MP.
Import ModusPonensRefinement ModusPonensRejection.
Theorem generated_protocol s logical bs ns i j p q first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  Protocol.theorem_at logical i = Some (SetTheory.implies p q) -> Protocol.theorem_at logical j = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final fid,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) (Protocol.OK (length (Protocol.history logical)))
      (Protocol.with_history logical (Protocol.history logical ++ [fid])) /\
    nth_error (Protocol.formulas logical) fid = Some q /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (Protocol.with_history logical (Protocol.history logical ++ [fid])) /\ flow 0 s final (Protocol.OK (length (Protocol.history logical))) tail.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Himp Hante Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  assert (Hopword : Z.of_nat 12 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReadsTwoFull.generated_reads s (fun _ => false) (fun _ => 0) 12 49 [50] i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hiword Hjword Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as Hreads.
  destruct Hreads as [Hopcode [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror
    [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := argument_state s i middle_separator j last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (20 <= length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  change (meta_value arg 8 = 0) in Hargerror.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s 49 [50] i middle_separator j last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Harg_classes : ClassStorage.represents arg (Protocol.formulas logical) (Protocol.classes logical)) by now apply argument_classes.
  destruct (HistoryLookup.modus_ponens_nodes arg logical i j p q Harg_arena Harg_history Himp Hante)
    as [node [aid [bid [Hbi [Hbj [Hnode [Hni [Hnj [Htuple Hlookup]]]]]]]]].
  assert (Hile : (i < length (Protocol.history logical))%nat).
  { unfold Protocol.theorem_at in Himp. destruct (nth_error (Protocol.history logical) i) as [f|] eqn:Hentry; [apply nth_error_Some; congruence|discriminate]. }
  assert (Hjle : (j < length (Protocol.history logical))%nat).
  { unfold Protocol.theorem_at in Hante. destruct (nth_error (Protocol.history logical) j) as [f|] eqn:Hentry; [apply nth_error_Some; congruence|discriminate]. }
  assert (Hiref : Z.of_nat i < meta_value arg 3) by (rewrite (proj1 Harg_history); lia).
  assert (Hjref : Z.of_nat j < meta_value arg 3) by (rewrite (proj1 Harg_history); lia).
  set (final := HistoryStorage.result arg (length (Protocol.history logical)) (Z.of_nat bid)).
  pose proof (ModusPonensExecution.generated_modusPonens arg (fun _ => false) (CommandMPExecution.arguments (Z.of_nat i) (Z.of_nat j))
    (length (Protocol.history logical)) i j node (Z.of_nat aid) (Z.of_nat bid) observations
    ltac:(lia) Hargbuffer Hargerror (proj1 Harg_history) Hbound Hbi Hbj Hnode Hni Hnj Htuple eq_refl eq_refl) as Hmp.
  assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (unfold final; rewrite HistoryStorage.result_meta_length; lia).
  assert (Hfinalerror : meta_value final 8 = 0) by (unfold final; rewrite HistoryStorage.result_meta_other by lia; exact Hargerror).
  pose proof (CommandMPExecution.generated_command s bs ns _ _ arg final (Z.of_nat i) (Z.of_nat j) observations _
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hargmeta Hargnumber Hargvalid Hargerror
    Hiref Hjref Hmp Hfinalmeta Hfinalerror) as Hrun.
  rewrite Hinput, Houtput in Hrun. exists final,bid. split; [exact Hrun|].
  assert (Hunique : NoDup (Protocol.formulas logical)) by (now apply (SemanticFrames.arena_NoDup s)).
  split.
  - eapply Protocol.step_accept with (t := Protocol.with_history logical (Protocol.history logical ++ [bid])).
    + eapply Protocol.accept_proof with (p := q).
      * now apply (Protocol.req_mp logical i j p q).
      * split; [exists []; now rewrite app_nil_r|]. split; [exact Hunique|]. split; [exact Hlookup|]. exists []; now rewrite app_nil_r.
    + now apply HistoryRefinement.retained_refl.
  - split; [exact Hlookup|]. split; [now apply HistoryStorage.result_arena|].
    split;[now apply HistoryStorage.result_classes|]. split;[apply HistoryStorage.append_represents;[lia|exact Harg_history]|].
    apply history_flow;[exact (read_two_frame s 49 [50] i middle_separator j last_separator tail Hmeta Hinput Houtput)|exact Herror|lia|exact (proj1 Harg_history)].
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
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 0 s final Protocol.NO tail.
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
  - split;[now apply argument_classes|]. split;[exact Harg_history|].
    apply no_flow;[exact (read_two_frame s 49 [50] i middle_separator j last_separator tail Hmeta Hinput Houtput)|exact Herror].
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
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 0 s final Protocol.NO tail.
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
  - split;[now apply argument_classes|]. split;[exact Harg_history|].
    apply no_flow;[exact (read_two_frame s 49 [50] i middle_separator j last_separator tail Hmeta Hinput Houtput)|exact Herror].
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
    ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\ HistoryRefinement.represents final next /\ LogicalHistory.valid next /\ flow 0 s final reply tail.
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
           destruct (generated_protocol s logical bs ns i j pante q first_separator prefix1 middle_separator prefix2 last_separator tail observations
             Hmeta Htoken Hbuffer Hpending Herror Hbound Hiword Hjword Himp Hante Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
             as [final [fid [Hrun [Hstep [Hfid [Hnextarena [Hnextclasses [Hnexthistory Hflow]]]]]]]].
           exists final,(Protocol.OK (length (Protocol.history logical))),(Protocol.with_history logical (Protocol.history logical ++ [fid])).
           split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Hnextarena|]. split; [exact Hnextclasses|].
           split;[exact Hnexthistory|]. split;[eapply LogicalHistory.step_valid;eassumption|exact Hflow].
        -- destruct (generated_guard_protocol s logical bs ns i j node aid tag left right first_separator prefix1 middle_separator prefix2 last_separator tail observations
             Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hlookupi Hlookupj Htuple (or_intror Hleft) Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
             as [final [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]].
           exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split;[exact Hc|]. split;[exact Hh|]. split;assumption.
      * destruct (generated_guard_protocol s logical bs ns i j node aid tag left right first_separator prefix1 middle_separator prefix2 last_separator tail observations
          Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hlookupi Hlookupj Htuple (or_introl Htag) Hvalid Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
          as [final [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]].
        exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split;[exact Hc|]. split;[exact Hh|]. split;assumption.
    + destruct (generated_invalid_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
        Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword (or_intror Hlookupj) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
        as [final [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]].
      exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split;[exact Hc|]. split;[exact Hh|]. split;assumption.
  - destruct (generated_invalid_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
      Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword (or_introl Hlookupi) Harena Hclasses Hhistory Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin)
      as [final [Hrun [Hstep [Ha [Hc [Hh Hflow]]]]]].
    exists final,Protocol.NO,logical. split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Ha|]. split;[exact Hc|]. split;[exact Hh|]. split;assumption.
Qed.
End MP.
Theorem generated_MP s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = 50 :: first_separator :: prefix1 ++ decimalBytes i ++ middle_separator :: prefix2 ++ decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) reply next /\
    NativeState.represents final next /\ LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next) /\
    boundary 0 s logical final reply next tail /\ Protocol.formulas next=Protocol.formulas logical.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hi Hj Hbound Hvalid Hstate Hfirst Hmiddle Hlast Hprefix1 Hprefix2 Hinput.
 destruct (MP.generated_total_protocol s logical bs ns i j first_separator prefix1 middle_separator prefix2 last_separator tail observations
   Hmeta Htoken Hprint Hpending Herror Hi Hj Hbound Hvalid (NativeState.formula_representation _ _ Hstate)
   (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate) Hfirst Hmiddle Hlast Hprefix1 Hprefix2 Hinput)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & HnextValid & Hflow).
 assert (Hnext:NativeState.represents final next).
 { exact (NativeProtocolLift.canonical 12 49 [50] s bs ns first_separator
   (prefix1++decimalBytes i++middle_separator::prefix2++decimalBytes j++last_separator::tail) observations final _ logical (Protocol.Req 12 [i;j] []) reply next
   ltac:(lia) ltac:(lia) ltac:(unfold NativeStateFrames.nonbinding;repeat split;lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput
   Hrun Hstate Hstep Harena Hclasses Hhistory). }
 pose proof (boundary_from_flow 0 s final bs ns logical next reply tail observations _ Hstate Hnext Htoken Hprint Hrun Hflow) as Hboundary.
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[exact HnextValid|]. split.
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
 - split;[exact Hboundary|]. apply (zero_formula_growth logical (Protocol.Req 12 [i;j] []) reply next Hstep).
   destruct Hboundary as [_ [Hgrowth _]]. now rewrite Nat.add_0_r in Hgrowth.
Qed.
End NativeWhitespaceMPBoundary.
