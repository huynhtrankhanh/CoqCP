From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStateFrames NativeProtocolLift NativeTheoremBoundary
 ReadOne TokenByte InternBounded Intern InternGrowth Observation FormulaEncoding Representation ArenaFrame ClassStorage
 HistoryRefinement HistoryLookup HistoryStorage LogicalHistory SemanticFrames Generalize GeneralizeRefinement GeneralizeTotal
 CommandGeneralize ReplyOK ReplyNO NativeGeneralizeBoundary FormulaTopology HashTable ClassSetInput ClassAbstractInput ClassLookup.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import NativeArgumentReads.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedAllocationInvariant.
Import IndexExecution SipHashExecution NativeTheoremBoundary GeneralizeRefinement NativeGeneralizeBoundary.
Lemma set_good native fs classes value sep tail : ClassStorage.represents native fs classes -> ClassLookup.wellformed native ->
 Z.of_nat value<=maximum -> ClassLookup.wellformed(ClassSetInput.result native(length classes)value sep tail).
Proof.
 intros Hclasses Hgood Hword. unfold ClassLookup.wellformed,ClassSetInput.result.
 rewrite ClassStorage.result_classes,ClassStorage.written_app.
 - rewrite ClassSetInput.argument_other by discriminate. apply Forall_app. split;[exact Hgood|].
   constructor;[cbn [snd];unfold word;split;lia|constructor].
 - rewrite ClassSetInput.argument_other by discriminate. exact(ClassStorage.represents_length _ _ _ Hclasses).
Qed.
Lemma abstract_good native fs classes value sep tail : ClassStorage.represents native fs classes -> ClassLookup.wellformed native ->
 Z.of_nat value<=maximum -> ClassLookup.wellformed(ClassAbstractInput.result native(length classes)value sep tail).
Proof.
 intros Hclasses Hgood Hword. unfold ClassLookup.wellformed,ClassAbstractInput.result,ClassAbstractInput.argument_state.
 rewrite ClassStorage.result_classes,ClassStorage.written_app.
 - rewrite ReadOne.argument_other by discriminate. apply Forall_app. split;[exact Hgood|].
   constructor;[cbn [snd];unfold word;split;lia|constructor].
 - rewrite ReadOne.argument_other by discriminate. exact(ClassStorage.represents_length _ _ _ Hclasses).
Qed.
Lemma set_top native count classes value sep tail : FormulaTopology.ordered native count ->
 FormulaTopology.ordered(ClassSetInput.result native classes value sep tail)count.
Proof.
 intro Htop. eapply FormulaTopology.same;[exact Htop|]. intros parent Hparent.
 unfold HashTableInvariant.tuple_at,ClassSetInput.result.
 rewrite ClassStorage.result_other by discriminate. now rewrite ClassSetInput.argument_other by discriminate.
Qed.
Lemma abstract_top native count classes value sep tail : FormulaTopology.ordered native count ->
 FormulaTopology.ordered(ClassAbstractInput.result native classes value sep tail)count.
Proof.
 intro Htop. eapply FormulaTopology.same;[exact Htop|]. intros parent Hparent.
 unfold HashTableInvariant.tuple_at,ClassAbstractInput.result,ClassAbstractInput.argument_state.
 rewrite ClassStorage.result_other by discriminate. now rewrite ReadOne.argument_other by discriminate.
Qed.
Theorem generalize_protocol s logical bs ns value p first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum ->
  FormulaTopology.ordered s (length(Protocol.formulas logical)) ->
  Protocol.theorem_at logical value = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))); unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs index) /\ flow 1 s final (Protocol.OK (length (Protocol.history logical))) tail /\ FormulaTopology.ordered final (length fs).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Htop Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta) Harena). }
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  destruct (HistoryLookup.theorem_lookup arg logical value p Harg_history Hlookup) as [fid [Hentry [Hformula [Hnative Hnth]]]].
  destruct (HistoryLookup.formula_reference arg _ fid p Harg_arena Hformula) as [_ [Hfidword _]].
  assert (Hreference : Z.of_nat value < meta_value arg 3).
  { rewrite (proj1 Harg_history). assert (value < length (Protocol.history logical))%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hnormal : FormulaEncoding.normal (4,Z.of_nat fid,0)) by (right; right; split; [reflexivity|]; split; [exact Hfidword|reflexivity]).
  assert (Hdecode : FormulaEncoding.decode (Protocol.formulas logical) (4,Z.of_nat fid,0) = Some (SetTheory.all p)).
  { change (option_map SetTheory.all (nth_error (Protocol.formulas logical) (Z.to_nat (Z.of_nat fid))) = Some (SetTheory.all p)).
    unfold Protocol.formula_at in Hformula. now rewrite Nat2Z.id, Hformula. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (GeneralizeExecution.arguments (Z.of_nat fid))
    (Protocol.formulas logical) (SetTheory.all p) Harg_arena Hargerror Hbound Hnormal Hdecode)
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula_result Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (GeneralizeExecution.arguments (Z.of_nat fid)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  assert(HargTop:FormulaTopology.ordered arg(length(Protocol.formulas logical))).
  { eapply FormulaTopology.same;[exact Htop|]. intros parent Hparent.
    unfold HashTableInvariant.tuple_at,arg,argument_state. now rewrite ReadOne.argument_other by discriminate. }
  assert(HnextTop:FormulaTopology.ordered internstate (length fs)).
  { destruct(FormulaTopology.generated_intern_preserves arg (fun _=>false) (GeneralizeExecution.arguments(Z.of_nat fid))
      (Protocol.formulas logical) (SetTheory.all p) Harg_arena HargTop Hargerror Hbound Hdecode)
      as (other & HotherRun & HotherError & HotherTop).
    assert(Hsame:other=internstate) by (rewrite Hintern in HotherRun;congruence). subst other.
    pose proof(proj1(proj2(proj1 Hnext))) as Hcount. change(meta_value internstate 1=Z.of_nat(length fs)) in Hcount.
    rewrite Hcount,Nat2Z.id in HotherTop. exact HotherTop. }
  pose proof (InternGrowth.at_most_one arg internstate (fun _=>false) (GeneralizeExecution.arguments (Z.of_nat fid))
    (Protocol.formulas logical) fs Harg_arena Hargerror Hbound Hintern Hnext) as Hgrowth.
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). exact Hargbuffer. }
  assert (Hintern_history : HistoryRefinement.represents internstate logical) by (eapply SemanticFrames.intern_history; eassumption).
  set (final := HistoryStorage.result internstate (length (Protocol.history logical)) (Z.of_nat index)).
  pose proof (GeneralizeExecution.generated_generalize arg (fun _ => false) (CommandGeneralizeExecution.arguments (Z.of_nat value)) internstate
    (length (Protocol.history logical)) value (Z.of_nat fid) index observations Hnative Hnth eq_refl Hobserved
    ltac:(lia) Hpostbuffer Hflag (proj1 Hintern_history) Hhistorybound Hresult) as Hgen.
  assert (Hfinalmeta : (8 < length (memory final arraydef_0__meta))%nat) by (unfold final; rewrite HistoryStorage.result_meta_length; lia).
  assert (Hfinalerror : meta_value final 8 = 0) by (unfold final; rewrite HistoryStorage.result_meta_other by lia; exact Hflag).
  pose proof (CommandGeneralizeExecution.generated_command s bs ns _ arg final (Z.of_nat value) observations _
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference Hgen Hfinalmeta Hfinalerror) as Hrun.
  rewrite Hintern_input, Hintern_output, Hinput, Houtput in Hrun.
  exists final,index,fs. split; [exact Hrun|].
  assert (Hunique : NoDup fs) by (now apply (SemanticFrames.arena_NoDup internstate)).
  split.
  - eapply Protocol.step_accept with (t := logical_after logical fs index).
    + unfold logical_after, logical_before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 13 [value] []) (SetTheory.all p) fs (Protocol.classes logical) index).
      * now apply (Protocol.req_gen logical value p).
      * split; [exact Hextends|]. split; [exact Hunique|]. split; [exact Hformula_result|]. exists []; now rewrite app_nil_r.
    + now apply HistoryRefinement.retained_refl.
  - split; [now apply HistoryStorage.result_arena|]. split.
    + apply HistoryStorage.result_classes. destruct Hextends as [extra ->].
      apply (SemanticFrames.intern_classes arg internstate); [exact Hframe|]. now apply argument_classes.
    + split;[exact (HistoryStorage.append_represents internstate (logical_before_append logical fs) index ltac:(lia) Hintern_history)|].
      split;[exact (intern_history_flow s arg internstate (Protocol.formulas logical) fs (length (Protocol.history logical)) (Z.of_nat index) tail
       (read_one_frame s 49 [51] value last_separator tail Hmeta Hinput Houtput) Hframe Harg_arena Hnext Hgrowth Hflag ltac:(lia) (proj1 Hintern_history))|].
      unfold final. eapply FormulaTopology.same;[exact HnextTop|]. intros parent Hparent.
      unfold HashTableInvariant.tuple_at. now rewrite HistoryStorage.result_other by discriminate.
Qed.
End NativeSpacedAllocationInvariant.
