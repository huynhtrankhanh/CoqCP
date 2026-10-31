From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput TokenByte NativeState NativeBasicDispatcher NativeBasicInvariant NativeBasicCountInvariant
 NativeSimpleCommands NativeSimpleInvariant NativeAllocationInvariant NativeNameGrowth NativeCommandBoundary NativeGeneralizeBoundary NativeTheoremBoundary
 LogicalNames LogicalHistory LogicalStorageMonotone LogicalRegistryBounds Representation ClassStorage ClassLookup FormulaTopology HashTable
 ClassSetInput ClassAbstractInput GeneralizeTotal ArenaFrame ReadOne ReadTwo HistoryRefinement HistoryLookup GeneralizeRefinement CommandGeneralize SemanticFrames ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import NativeArgumentReads NativeSpacedAllocationInvariant.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedGeneralizeTopology.
Import IndexExecution SipHashExecution.
Lemma formula_count native logical : NativeState.represents native logical -> meta_value native 1=Z.of_nat(length(Protocol.formulas logical)).
Proof. intro Hstate. exact (proj1(proj2(proj1(NativeState.formula_representation _ _ Hstate)))). Qed.
Lemma arena_count native fs : NativeRepresentation.canonical_arena native fs -> meta_value native 1=Z.of_nat(length fs).
Proof. intro Harena. exact(proj1(proj2(proj1 Harena))). Qed.
Lemma same_formula_count native logical fs : NativeState.represents native logical -> NativeRepresentation.canonical_arena native fs ->
 length(Protocol.formulas logical)=length fs.
Proof. intros Hstate Harena. pose proof(formula_count _ _ Hstate). pose proof(arena_count _ _ Harena). lia. Qed.
Module Generalize.
Import NativeGeneralizeBoundary NativeTheoremBoundary GeneralizeRefinement.
Theorem generalize_rejected_top s logical bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> nth_error (Protocol.history logical) value = None ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = 51 :: first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\ HistoryRefinement.represents final logical /\ flow 1 s final Protocol.NO tail /\ (FormulaTopology.ordered s (length(Protocol.formulas logical)) -> FormulaTopology.ordered final(length(Protocol.formulas logical))).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hspaces Hin.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat value).
  { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
  pose proof (CommandGeneralizeExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists (ReplyNOExecution.reply_state arg). split; [exact Hrun|].
  split; [apply GeneralizeTotal.logical_rejected; [exact Hlookup|now apply (SemanticFrames.arena_NoDup s)]|].
  split.
  - eapply ArenaFrame.storage_arena; [|exact Harena]. eapply ArenaFrame.storage_trans;
      [exact (ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta)|apply ArenaFrame.storage_output].
  - split;[now apply argument_classes|]. split;[exact Harg_history|].
    split.
    + apply (flow_weaken 0 1 s _ Protocol.NO tail ltac:(lia)).
      apply no_flow;[exact (read_one_frame s 49 [51] value last_separator tail Hmeta Hinput Houtput)|exact Herror].
    + intro Htop. eapply NativeSimpleInvariant.storage_top;[|exact Htop].
      change(memory arg arraydef_0__formulas=memory s arraydef_0__formulas).
      unfold arg,argument_state. apply ReadOne.argument_other;discriminate.
Qed.
End Generalize.

Lemma generalize_top native logical value bs ns first_separator spaces last_separator tail observations final trace next :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat -> meta_value native 15=50 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 -> Z.of_nat(length(Protocol.history logical))<maximum ->
 Z.of_nat value<=maximum -> LogicalHistory.valid logical ->
 TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
 stdin native=51::first_separator::spaces++decimalBytes value++last_separator::tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 FormulaTopology.ordered final(length(Protocol.formulas next)) /\ (length(Protocol.formulas next)<=S(length(Protocol.formulas logical)))%nat.
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hword Hhistory Hfirst Hlast Hspaces Hinput Hrun Hstate Hnext Htop.
 pose proof(NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof(NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof(NativeState.history_representation _ _ Hstate) as Htheorems.
 destruct(nth_error(Protocol.history logical)value) as [fid|] eqn:Hlookup.
 - destruct(Hhistory value fid Hlookup) as [p Hp].
   assert(Htheorem:Protocol.theorem_at logical value=Some p) by (unfold Protocol.theorem_at;now rewrite Hlookup).
   destruct(NativeSpacedAllocationInvariant.generalize_protocol native logical bs ns value p first_separator spaces last_separator tail observations
     Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hword Htop Htheorem Harena Hclasses Htheorems
     Hfirst Hlast Hspaces Hinput)
     as(model & index & fs & HmodelRun & Hstep & HmodelArena & HmodelClasses & HmodelHistory & Hflow & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   pose proof(same_formula_count _ _ _ Hnext HmodelArena) as Hcount.
   split;[now rewrite Hcount|].
   destruct Hflow as (Hin & Hout & Herror' & Hstop & Hgrowth & Hrest).
   pose proof(formula_count _ _ Hstate). pose proof(formula_count _ _ Hnext). lia.
 - destruct(Generalize.generalize_rejected_top native logical bs ns value first_separator spaces last_separator tail observations
     Hmeta Htoken Hprint Hpending Herror Hword Hlookup Harena Hclasses Htheorems
     Hfirst Hlast Hspaces Hinput)
     as(model & HmodelRun & Hstep & HmodelArena & HmodelClasses & HmodelHistory & Hflow & HmodelTop).
   assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
   pose proof(same_formula_count _ _ _ Hnext HmodelArena) as Hcount.
   split;[rewrite Hcount;now apply HmodelTop|lia].
Qed.
End NativeSpacedGeneralizeTopology.
