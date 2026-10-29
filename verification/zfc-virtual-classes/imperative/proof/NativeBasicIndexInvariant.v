From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import LogicalRegistryBounds NativeBasicInvariant NativeBasicCommandInvariant NativeBasicCountInvariant NativeBasicDispatcher NativeAllocationInvariant NativeGeneralizeBoundary NativeTheoremBoundary GeneralizeRefinement GeneralizeTotal CommandGeneralize Generalize HistoryLookup HistoryStorage LogicalHistory NativeSimpleInvariant SchemaEvaluationIndexBounds SchemaEvaluationIndexCell SchemaEvaluationIndexShiftClass RenameMemoInput RenameMemoIndexBounds NativeSimpleCommands FormulaTopology HashTable ClassLookup Index SipHash DecimalInput CommandArgs CommandInput ReadOne ReadTwo TokenByte InternBounded InternGrowth Intern Observation
 FormulaEncoding Representation ArenaFrame FormulaProjection ClassStorage ClassSetInput ClassAbstractInput HistoryRefinement SemanticFrames
 FormulaAtoms FormulaImp FormulaAll ReplyOK ReplyNO NativeState NativeStateFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeBasicIndexInvariant.
Import IndexExecution SipHashExecution.
Module Bounds := SchemaEvaluationIndexBounds.
Definition set_indices (native:Machine) bound := Forall (fun raw:Z*Z=>fst raw=0 -> (Z.to_nat(snd raw)<=bound)%nat) (memory native arraydef_0__classes).
Lemma source_set_indices native fs classes bound : ClassStorage.represents native fs classes -> Bounds.classes bound classes -> set_indices native bound.
Proof.
 intros [_ Hrep] Hclasses. unfold set_indices.
 induction Hrep as [|[tag value] cls raws classes Hdecode Hrep IH] in Hclasses|-*;[constructor|].
 inversion Hclasses as [|cls' classes' Hbound Htail];subst cls' classes'. constructor.
 - cbn [fst snd]. intro Htag. subst tag. change(Some(VirtualClasses.set(Z.to_nat value))=Some cls) in Hdecode.
   injection Hdecode as <-. exact Hbound.
 - now apply IH.
Qed.
Lemma classes_of_raw native fs classes bound : ClassStorage.represents native fs classes -> Bounds.formulas bound fs ->
 set_indices native bound -> Bounds.classes bound classes.
Proof.
 intros [_ Hrep] Hfs Hsets. unfold set_indices in Hsets.
 induction Hrep as [|[tag value] cls raws classes Hdecode Hrep IH] in Hsets|-*;[constructor|].
 inversion Hsets as [|raw raws' Hset Htail];subst raw raws'. constructor;[|now apply IH].
 unfold ClassStorage.decode in Hdecode. destruct(Z.eq_dec tag 0) as [->|H0].
 - injection Hdecode as <-. apply Hset;reflexivity.
 - destruct(Z.eq_dec tag 1) as [->|H1];[|discriminate].
   destruct(nth_error fs(Z.to_nat value)) as [p|] eqn:Hp;[|discriminate].
   injection Hdecode as <-. exact(Bounds.formula_lookup bound fs (Z.to_nat value) p Hfs Hp).
Qed.
Lemma set_indices_mono native lower upper : (lower<=upper)%nat -> set_indices native lower -> set_indices native upper.
Proof. intros Hle Hset. eapply Forall_impl;[exact Hset|]. intros [tag value] Hraw Htag. specialize(Hraw Htag). lia. Qed.
Lemma bounded_final native logical bound : NativeState.represents native logical -> FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 Bounds.raw_arena native(length(Protocol.formulas logical))bound -> set_indices native bound ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)bound.
Proof.
 intros Hstate Htop Hraw Hsets. split;[exact Hraw|]. eapply classes_of_raw;[exact(NativeState.class_representation _ _ Hstate)| |exact Hsets].
 exact(Bounds.canonical_raw_formulas native _ bound (NativeState.formula_representation _ _ Hstate) Htop Hraw).
Qed.
Module Atoms.
Import NativeSimpleInvariant.Atoms.
Theorem accepted_raw opcode ch chars s logical bs ns a b first_separator middle last tail observations index_bound :
  (opcode = 1%nat \/ opcode = 2%nat) -> decimalBytes opcode = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  (a<=index_bound)%nat -> (b<=index_bound)%nat ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes(Protocol.OK index);unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final fs /\ Bounds.raw_arena final(length fs)index_bound.
Proof.
  intros Hcase Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb Hnative Hsep1 Hsep2 Hsep3 Hin.
  intros Hraw HaBound HbBound.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat opcode <= maximum) by (unfold maximum; destruct Hcase; subst opcode; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) opcode ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hnormal : FormulaEncoding.normal (Z.of_nat opcode,Z.of_nat a,Z.of_nat b)).
  { right. left. split; [destruct Hcase; subst opcode; cbn; tauto|]. unfold word. split; lia. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (atom opcode a b) Harg_arena Hseconderror Hbound Hnormal (decoded _ _ _ _ Hcase))
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hsecondbuffer. }
  assert (Htag : Z.of_nat opcode = 1 \/ Z.of_nat opcode = 2) by (destruct Hcase; subst opcode; cbn; auto).
  pose proof (FormulaAtomsExecution.generated_command (Z.of_nat opcode) s bs ns _ _ arg internstate index (Z.of_nat a) (Z.of_nat b) observations
    Htag Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  assert(HargRaw:Bounds.raw_arena arg(length(Protocol.formulas logical))index_bound).
  { eapply Bounds.raw_array_frame;[|exact Hraw]. unfold arg. apply ReadTwo.second_other;discriminate. }
  assert(HnewRaw:RenameMemoInput.raw_bound index_bound ((FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_tag,(FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_a,(FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_b)).
  { change(RenameMemoInput.raw_bound index_bound (Z.of_nat opcode,Z.of_nat a,Z.of_nat b)). unfold RenameMemoInput.raw_bound. rewrite !Nat2Z.id. intros Hatomic. split;assumption. }
  pose proof(Bounds.observed_intern arg internstate (fun _=>false) (FormulaAtomsExecution.arguments (Z.of_nat opcode) (Z.of_nat a) (Z.of_nat b)) (Protocol.formulas logical) fs index_bound observations observations
    Harg_arena Hseconderror Hbound HargRaw HnewRaw Hobserved Hnext) as HnextRaw.
  exists(ReplyOKExecution.reply_state internstate index),index,fs. split;[exact Hrun|]. split.
  - exact(FormulaProjection.storage_arena internstate _ fs (FormulaProjection.reply_storage internstate index) Hnext).
  - eapply Bounds.raw_array_frame;[apply ReplyOKExecution.reply_other;discriminate|exact HnextRaw].
Qed.
End Atoms.
Module Imp.
Import NativeSimpleInvariant.Imp.
Theorem accepted_raw ch chars s logical bs ns a b p q first_separator middle last tail observations index_bound :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  Protocol.formula_at logical a = Some p -> Protocol.formula_at logical b = Some q ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes(Protocol.OK index);unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final fs /\ Bounds.raw_arena final(length fs)index_bound.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbound Ha Hb HlookupA HlookupB Hnative Hsep1 Hsep2 Hsep3 Hin.
  intro Hraw.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hnormal : FormulaEncoding.normal (3,Z.of_nat a,Z.of_nat b)).
  { right. left. split; [right; right; reflexivity|]. unfold word. split; lia. }
  assert (HreferenceA : Z.of_nat a < meta_value arg 1) by (eapply reference; eassumption).
  assert (HreferenceB : Z.of_nat b < meta_value arg 1) by (eapply reference; eassumption).
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b))
    (Protocol.formulas logical) (SetTheory.implies p q) Harg_arena Hseconderror Hbound Hnormal (decoded _ _ _ _ _ HlookupA HlookupB))
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hsecondbuffer. }
  pose proof (FormulaImpExecution.generated_command s bs ns _ _ arg internstate index (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror
    HreferenceA HreferenceB Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  assert(HargRaw:Bounds.raw_arena arg(length(Protocol.formulas logical))index_bound).
  { eapply Bounds.raw_array_frame;[|exact Hraw]. unfold arg. apply ReadTwo.second_other;discriminate. }
  assert(HnewRaw:RenameMemoInput.raw_bound index_bound ((FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_tag,(FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_a,(FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)) vardef_0__intern_b)).
  { change(RenameMemoInput.raw_bound index_bound (3,Z.of_nat a,Z.of_nat b)). unfold RenameMemoInput.raw_bound. intros [Htag|Htag];discriminate. }
  pose proof(Bounds.observed_intern arg internstate (fun _=>false) (FormulaImpExecution.arguments (Z.of_nat a) (Z.of_nat b)) (Protocol.formulas logical) fs index_bound observations observations
    Harg_arena Hseconderror Hbound HargRaw HnewRaw Hobserved Hnext) as HnextRaw.
  exists(ReplyOKExecution.reply_state internstate index),index,fs. split;[exact Hrun|]. split.
  - exact(FormulaProjection.storage_arena internstate _ fs (FormulaProjection.reply_storage internstate index) Hnext).
  - eapply Bounds.raw_array_frame;[apply ReplyOKExecution.reply_other;discriminate|exact HnextRaw].
Qed.
End Imp.
Module All.
Import NativeSimpleInvariant.All.
Theorem accepted_raw s logical bs ns value p first_separator last_separator tail observations index_bound :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = Some p ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes(Protocol.OK index);unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final fs /\ Bounds.raw_arena final(length fs)index_bound.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hvalue Hlookup Hnative Hsep1 Hsep2 Hin.
  intro Hraw.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hfour : Z.of_nat 4 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 4 52 [] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hfour eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadOne.argument_storage s 52 [] value last_separator tail Hmeta) Harena). }
  assert (Hreference : Z.of_nat value < meta_value arg 1).
  { pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hcount.
    change (meta_value arg 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    assert (Hindex : (value < length (Protocol.formulas logical))%nat).
    { apply nth_error_Some. unfold Protocol.formula_at in Hlookup. congruence. }
    rewrite Hcount. lia. }
  assert (Hnormal : FormulaEncoding.normal (4,Z.of_nat value,0)).
  { right. right. repeat split; try reflexivity; try unfold word; lia. }
  assert (Hdecode : FormulaEncoding.decode (Protocol.formulas logical) (4,Z.of_nat value,0) = Some (SetTheory.all p)).
  { change (option_map SetTheory.all (nth_error (Protocol.formulas logical) (Z.to_nat (Z.of_nat value))) = Some (SetTheory.all p)).
    unfold Protocol.formula_at in Hlookup. now rewrite Nat2Z.id, Hlookup. }
  destruct (InternBounded.generated_refines arg (fun _ => false) (FormulaAllExecution.arguments (Z.of_nat value))
    (Protocol.formulas logical) (SetTheory.all p) Harg_arena Hargerror Hbound Hnormal Hdecode)
    as [internstate [fs [index [Hintern [Hframe [Hflag [Hresult [Hword [Hnext [Hformula Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern (fun _ => false) (FormulaAllExecution.arguments (Z.of_nat value)))
    (arg,observations) = Some (tt,(internstate,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern]. }
  pose proof Hframe as [Harrays [Hcells [Hintern_input Hintern_output]]].
  assert (Hpostmeta : (17 < length (memory internstate arraydef_0__meta))%nat).
  { pose proof (proj1 (proj1 (proj1 Hnext))) as Hcapacity. lia. }
  assert (Hpostbuffer : (20 <= length (memory internstate arraydef_0__printBuffer))%nat).
  { rewrite (Harrays arraydef_0__printBuffer ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    exact Hargbuffer. }
  pose proof (FormulaAllExecution.generated_command s bs ns _ arg internstate index (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference Hobserved Hpostmeta Hpostbuffer Hflag Hresult Hword) as Hrun.
  assert (Htail : stdin internstate = tail) by (rewrite Hintern_input; exact Hinput).
  assert (Hstdout : stdout internstate = stdout s) by (rewrite Hintern_output; exact Houtput).
  rewrite Htail, Hstdout in Hrun.
  assert(HargRaw:Bounds.raw_arena arg(length(Protocol.formulas logical))index_bound).
  { eapply Bounds.raw_array_frame;[|exact Hraw]. unfold arg. unfold argument_state. apply ReadOne.argument_other;discriminate. }
  assert(HnewRaw:RenameMemoInput.raw_bound index_bound ((FormulaAllExecution.arguments (Z.of_nat value)) vardef_0__intern_tag,(FormulaAllExecution.arguments (Z.of_nat value)) vardef_0__intern_a,(FormulaAllExecution.arguments (Z.of_nat value)) vardef_0__intern_b)).
  { change(RenameMemoInput.raw_bound index_bound (4,Z.of_nat value,0)). unfold RenameMemoInput.raw_bound. intros [Htag|Htag];discriminate. }
  pose proof(Bounds.observed_intern arg internstate (fun _=>false) (FormulaAllExecution.arguments (Z.of_nat value)) (Protocol.formulas logical) fs index_bound observations observations
    Harg_arena Hargerror Hbound HargRaw HnewRaw Hobserved Hnext) as HnextRaw.
  exists(ReplyOKExecution.reply_state internstate index),index,fs. split;[exact Hrun|]. split.
  - exact(FormulaProjection.storage_arena internstate _ fs (FormulaProjection.reply_storage internstate index) Hnext).
  - eapply Bounds.raw_array_frame;[apply ReplyOKExecution.reply_other;discriminate|exact HnextRaw].
Qed.
End All.
Module Generalize.
Import NativeGeneralizeBoundary NativeTheoremBoundary GeneralizeRefinement.
Theorem generalize_raw s logical bs ns value p first_separator last_separator tail observations index_bound :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum ->
  FormulaTopology.ordered s (length(Protocol.formulas logical)) ->
  Protocol.theorem_at logical value = Some p ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final (index:nat) fs,
    execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes(Protocol.OK(length(Protocol.history logical)));unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final fs /\ Bounds.raw_arena final(length fs)index_bound.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Htop Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  intro Hraw.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
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
  assert(HargRaw:Bounds.raw_arena arg(length(Protocol.formulas logical))index_bound).
  { eapply Bounds.raw_array_frame;[|exact Hraw]. unfold arg,argument_state. apply ReadOne.argument_other;discriminate. }
  assert(HnewRaw:RenameMemoInput.raw_bound index_bound (4,Z.of_nat fid,0)).
  { unfold RenameMemoInput.raw_bound. intros [Htag|Htag];discriminate. }
  pose proof(Bounds.observed_intern arg internstate (fun _=>false) (GeneralizeExecution.arguments(Z.of_nat fid))
    (Protocol.formulas logical) fs index_bound observations observations Harg_arena Hargerror Hbound HargRaw HnewRaw Hobserved Hnext) as HnextRaw.
  exists final,index,fs. split;[exact Hrun|]. split;[now apply HistoryStorage.result_arena|].
  unfold final. eapply Bounds.raw_array_frame;[apply HistoryStorage.result_other;discriminate|exact HnextRaw].
Qed.
End Generalize.

Module ImpRejected.
Import NativeSimpleInvariant.Imp.
Theorem imp_rejected_raw ch chars s logical bs ns a b first_separator middle last tail observations index_bound :
  decimalBytes 3%nat = ch :: chars ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  (Protocol.formula_at logical a = None \/ Protocol.formula_at logical b = None) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final,
    execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    Bounds.raw_arena final(length(Protocol.formulas logical))index_bound.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hbad Hnative Hsep1 Hsep2 Hsep3 Hin.
  intro Hraw.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hcode : Z.of_nat 3 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadTwo.generated_reads s (fun _ => false) (fun _ => 0) 3 ch chars a b first_separator middle last tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin) as Hread.
  destruct Hread as [Hopcode [HreadA [HreadB [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer [Hsecondnumber [Hsecondvalid [Hseconderror [Hinput Houtput]]]]]]]]]]]]]]]]].
  set (arg := ReadTwo.second_state s ch chars a middle b last tail).
  assert (Harg_arena : NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { exact (ArenaFrame.storage_arena s arg _ (ReadTwo.second_storage s ch chars a middle b last tail Hmeta) Harena). }
  assert (Hbadrefs : meta_value arg 1 <= Z.of_nat a \/ meta_value arg 1 <= Z.of_nat b).
  { pose proof (proj1 (proj2 (proj1 Harg_arena))) as Hcount.
    change (meta_value arg 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    rewrite Hcount. destruct Hbad as [Hbad|Hbad]; unfold Protocol.formula_at in Hbad; apply nth_error_None in Hbad; lia. }
  pose proof (FormulaImpExecution.generated_rejected_command s bs ns _ _ arg (Z.of_nat a) (Z.of_nat b) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror HreadA Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror HreadB Hsecondmeta Hsecondnumber Hsecondvalid Hseconderror Hbadrefs) as Hrun.
  assert (Htail : stdin arg = tail) by exact Hinput.
  assert (Hstdout : stdout arg = stdout s) by exact Houtput.
  rewrite Htail, Hstdout in Hrun.
  exists(ReplyNOExecution.reply_state arg). split;[exact Hrun|]. split.
  - exact(ArenaFrame.storage_arena arg _ (Protocol.formulas logical) (ArenaFrame.storage_output _ _) Harg_arena).
  - eapply Bounds.raw_array_frame;[|exact Hraw]. change(memory arg arraydef_0__formulas=memory s arraydef_0__formulas).
    unfold arg. apply ReadTwo.second_other;discriminate.
Qed.
End ImpRejected.
Module AllRejected.
Import NativeSimpleInvariant.All.
Theorem all_rejected_raw s logical bs ns value first_separator last_separator tail observations index_bound :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 53 -> meta_value s 8 = 0 -> Z.of_nat value <= maximum ->
  Protocol.formula_at logical value = None -> NoDup (Protocol.formulas logical) ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final,
    execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    Bounds.raw_arena final(length(Protocol.formulas logical))index_bound.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Hunique Hnative Hsep1 Hsep2 Hin.
  intro Hraw.
  pose proof (NativeState.formula_representation _ _ Hnative) as Harena.
  pose proof (NativeState.class_representation _ _ Hnative) as Hclasses.
  pose proof (NativeState.history_representation _ _ Hnative) as Hhistory.
  assert (Hreference : meta_value s 1 <= Z.of_nat value).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    change (meta_value s 1 = Z.of_nat (length (Protocol.formulas logical))) in Hcount.
    pose proof Hlookup as Hindex. unfold Protocol.formula_at in Hindex. apply nth_error_None in Hindex.
    rewrite Hcount. lia. }
  exists(rejected s value last_separator tail). split.
  - exact(generated_rejected s bs ns value first_separator last_separator tail observations Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hin).
  - split;[now apply rejected_arena|]. eapply Bounds.raw_array_frame;[|exact Hraw].
    change(memory(argument_state s value last_separator tail)arraydef_0__formulas=memory s arraydef_0__formulas).
    unfold argument_state. apply ReadOne.argument_other;discriminate.
Qed.
End AllRejected.
Module GeneralizeRejected.
Import NativeGeneralizeBoundary NativeTheoremBoundary GeneralizeRefinement.
Theorem generalize_rejected_raw s logical bs ns value first_separator last_separator tail observations index_bound :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> nth_error (Protocol.history logical) value = None ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  Bounds.raw_arena s(length(Protocol.formulas logical))index_bound ->
  exists final,
    execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    Bounds.raw_arena final(length(Protocol.formulas logical))index_bound.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hlookup Harena Hclasses Hhistory Hsep1 Hsep2 Hin.
  intro Hraw.
  assert (Hopword : Z.of_nat 13 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 13 49 [51] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hopword eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  change (stdin arg = tail) in Hinput. change (stdout arg = stdout s) in Houtput.
  assert (Harg_history : HistoryRefinement.represents arg logical) by now apply argument_history.
  assert (Hreference : meta_value arg 3 <= Z.of_nat value).
  { rewrite (proj1 Harg_history). apply nth_error_None in Hlookup. lia. }
  pose proof (CommandGeneralizeExecution.generated_rejected_command s bs ns _ arg (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hreference) as Hrun.
  rewrite Hinput,Houtput in Hrun. exists(ReplyNOExecution.reply_state arg). split;[exact Hrun|]. split.
 - eapply ArenaFrame.storage_arena;[|exact Harena]. eapply ArenaFrame.storage_trans;
   [exact(ReadOne.argument_storage s 49 [51] value last_separator tail Hmeta)|apply ArenaFrame.storage_output].
 - eapply Bounds.raw_array_frame;[|exact Hraw]. change(memory arg arraydef_0__formulas=memory s arraydef_0__formulas).
   unfold arg,argument_state. apply ReadOne.argument_other;discriminate.
Qed.
End GeneralizeRejected.

Lemma raw_model native logical fs bound : NativeState.represents native logical -> NativeRepresentation.canonical_arena native fs ->
 Bounds.raw_arena native(length fs)bound -> Bounds.raw_arena native(length(Protocol.formulas logical))bound.
Proof. intros Hstate Harena Hraw. rewrite(NativeBasicCommandInvariant.same_formula_count _ _ _ Hstate Harena). exact Hraw. Qed.
Lemma raw_preserves native logical request bs ns tail observations final trace next index_bound :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.formulas logical))<=9223372036854775807 -> Z.of_nat(length(Protocol.history logical))<maximum ->
 NativeState.represents native logical -> NativeState.represents final next -> LogicalHistory.valid logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) ->
 Bounds.raw_arena native(length(Protocol.formulas logical))index_bound ->
 Forall (fun value=>(value<=index_bound)%nat)(Protocol.arguments request) ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Bounds.raw_arena final(length(Protocol.formulas next))index_bound.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hstate Hnext HhistoryValid Htop Hraw Hargs Hinput Hrun.
 pose proof(NativeBasicDispatcher.supported_bound _ Hsupported) as Hrange.
 destruct(le_dec (Protocol.opcode request) 4) as [Hsimple|Hcomplex].
 - destruct request as [opcode values name]. cbn [Protocol.opcode] in Hsimple,Hrange.
   assert(Hopcode:opcode=1%nat \/ opcode=2%nat \/ opcode=3%nat \/ opcode=4%nat) by lia.
   destruct Hopcode as [->|[->|[->| ->]]].
   + destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
     destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|a' values Ha Hrest];subst a' values.
     inversion Hrest as [|b' values Hb Hnil];subst b' values.
     inversion Hargs as [|a' values HaBound HargsRest];subst a' values.
     inversion HargsRest as [|b' values HbBound HargsNil];subst b' values.
     change(meta_value native 15=50) in Hpending.
     rewrite(NativeBasicDispatcher.two_rest 1 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
     change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct(Atoms.accepted_raw 1 49 [] native logical bs ns a b 32 32 10 tail observations index_bound
       ltac:(tauto) eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw HaBound HbBound)
       as(model & index & fs & HmodelRun & Harena & HmodelRaw).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     eapply raw_model;eassumption.
   + destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
     destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|a' values Ha Hrest];subst a' values.
     inversion Hrest as [|b' values Hb Hnil];subst b' values.
     inversion Hargs as [|a' values HaBound HargsRest];subst a' values.
     inversion HargsRest as [|b' values HbBound HargsNil];subst b' values.
     change(meta_value native 15=51) in Hpending.
     rewrite(NativeBasicDispatcher.two_rest 2 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
     change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct(Atoms.accepted_raw 2 50 [] native logical bs ns a b 32 32 10 tail observations index_bound
       ltac:(tauto) eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw HaBound HbBound)
       as(model & index & fs & HmodelRun & Harena & HmodelRaw).
     assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model.
     eapply raw_model;eassumption.
   + destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
     destruct values as [|a [|b [|bad values]]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|a' values Ha Hrest];subst a' values.
     inversion Hrest as [|b' values Hb Hnil];subst b' values.
     inversion Hargs as [|a' values HaBound HargsRest];subst a' values.
     inversion HargsRest as [|b' values HbBound HargsNil];subst b' values.
     change(meta_value native 15=52) in Hpending.
     rewrite(NativeBasicDispatcher.two_rest 3 a b tail ltac:(unfold NativeBasicDispatcher.two;tauto)) in Hinput.
     change(stdin native=32::decimalBytes a++32::decimalBytes b++10::tail) in Hinput.
     destruct(Protocol.formula_at logical a) as [p|] eqn:Hp;
       destruct(Protocol.formula_at logical b) as [q|] eqn:Hq.
     * destruct(Imp.accepted_raw 51 [] native logical bs ns a b p q 32 32 10 tail observations index_bound
        eq_refl Hmeta Htoken Hprint Hpending Herror Hroom Ha Hb Hp Hq Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & index & fs & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
     * destruct(ImpRejected.imp_rejected_raw 51 [] native logical bs ns a b 32 32 10 tail observations index_bound
        eq_refl Hmeta Htoken Hprint Hpending Herror Ha Hb (or_intror Hq) Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
     * destruct(ImpRejected.imp_rejected_raw 51 [] native logical bs ns a b 32 32 10 tail observations index_bound
        eq_refl Hmeta Htoken Hprint Hpending Herror Ha Hb (or_introl Hp) Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
     * destruct(ImpRejected.imp_rejected_raw 51 [] native logical bs ns a b 32 32 10 tail observations index_bound
        eq_refl Hmeta Htoken Hprint Hpending Herror Ha Hb (or_introl Hp) Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
   + destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
     destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|value' values Hword Hnil];subst value' values.
     change(meta_value native 15=53) in Hpending.
     rewrite(NativeBasicDispatcher.one_rest 4 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
     change(stdin native=32::decimalBytes value++10::tail) in Hinput.
     destruct(Protocol.formula_at logical value) as [p|] eqn:Hp.
     * destruct(All.accepted_raw native logical bs ns value p 32 10 tail observations index_bound
        Hmeta Htoken Hprint Hpending Herror Hroom Hword Hp Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & index & fs & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
     * destruct(AllRejected.all_rejected_raw native logical bs ns value 32 10 tail observations index_bound
        Hmeta Htoken Hprint Hpending Herror Hword Hp (SemanticFrames.arena_NoDup _ _ (NativeState.formula_representation _ _ Hstate))
        Hstate ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw)
        as(model & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
 - destruct(Nat.eq_dec(Protocol.opcode request)13%nat) as [H13|H13].
   + destruct request as [opcode values name]. cbn [Protocol.opcode] in H13. subst opcode.
     destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname. subst name.
     destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|value' values Hword Hnil];subst value' values.
     change(meta_value native 15=50) in Hpending.
     rewrite(NativeBasicDispatcher.one_rest 13 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
     change(stdin native=51::32::decimalBytes value++10::tail) in Hinput.
     pose proof(NativeState.formula_representation _ _ Hstate) as HsourceArena.
     pose proof(NativeState.class_representation _ _ Hstate) as HsourceClasses.
     pose proof(NativeState.history_representation _ _ Hstate) as HsourceHistory.
     destruct(nth_error(Protocol.history logical)value) as [fid|] eqn:Hlookup.
     * destruct(HhistoryValid value fid Hlookup) as [p Hp].
       assert(Htheorem:Protocol.theorem_at logical value=Some p) by (unfold Protocol.theorem_at;now rewrite Hlookup).
       destruct(Generalize.generalize_raw native logical bs ns value p 32 10 tail observations index_bound
        Hmeta Htoken Hprint Hpending Herror Hroom HhistoryRoom Hword Htop Htheorem HsourceArena HsourceClasses HsourceHistory
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw) as(model & index & fs & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
     * destruct(GeneralizeRejected.generalize_rejected_raw native logical bs ns value 32 10 tail observations index_bound
        Hmeta Htoken Hprint Hpending Herror Hword Hlookup HsourceArena HsourceClasses HsourceHistory
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput Hraw) as(model & HmodelRun & Harena & HmodelRaw).
       assert(Hsame:model=final) by (rewrite Hrun in HmodelRun;congruence). subst model. eapply raw_model;eassumption.
   + pose proof(NativeBasicCommandInvariant.request_count native request bs ns tail observations final trace Hshape Hsupported
      ltac:(unfold NativeBasicCountInvariant.unchanged;repeat split;lia) Hmeta Htoken Hpending Herror Hinput Hrun) as Hcount.
     pose proof(NativeBasicCommandInvariant.formula_count _ _ Hstate) as Hbefore.
     pose proof(NativeBasicCommandInvariant.formula_count _ _ Hnext) as Hafter.
     assert(Hlength:length(Protocol.formulas next)=length(Protocol.formulas logical)) by lia. rewrite Hlength.
     eapply Bounds.raw_array_frame;[|exact Hraw]. eapply NativeBasicCommandInvariant.request_array;try eassumption.
     * unfold NativeBasicInvariant.Arrays.kind;tauto.
     * unfold NativeBasicInvariant.Arrays.unchanged. repeat split;intro H;try discriminate;repeat split;lia.
Qed.

Lemma sets_frame before after bound : memory after arraydef_0__classes=memory before arraydef_0__classes ->
 set_indices before bound -> set_indices after bound.
Proof. unfold set_indices;intros -> H;exact H. Qed.
Lemma allocated_sets native count entry bound : length(memory native arraydef_0__classes)=count ->
 set_indices native bound -> (fst entry=0 -> (Z.to_nat(snd entry)<=bound)%nat) ->
 set_indices(ClassStorage.result native count entry)bound.
Proof.
 intros Hlength Hsets Hentry. unfold set_indices. rewrite ClassStorage.result_classes,ClassStorage.written_app by exact Hlength.
 apply Forall_app. split;[exact Hsets|constructor;[exact Hentry|constructor]].
Qed.
Lemma sets_preserves native logical request bs ns tail observations final trace next index_bound :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 Z.of_nat(length(Protocol.classes logical))<maximum ->
 Forall(fun value=>(value<=index_bound)%nat)(Protocol.arguments request) ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 NativeState.represents native logical -> NativeState.represents final next -> set_indices native index_bound -> set_indices final index_bound.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hroom Hargs Hinput Hrun Hstate Hnext Hsets.
 destruct(Nat.eq_dec (Protocol.opcode request) 5%nat) as [H5|H5].
 - destruct request as [opcode values name]. cbn [Protocol.opcode] in H5. subst opcode.
   destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
   destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
   inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   inversion Hargs as [|value' values HvalueBound HnilBound];subst value' values.
   change(meta_value native 15=54) in Hpending.
   rewrite(NativeBasicDispatcher.one_rest 5 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
   change(stdin native=32::decimalBytes value++10::tail) in Hinput.
   pose proof(ClassSetInput.generated_pending native bs ns (length(Protocol.classes logical)) value 32 10 tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue
    ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
   assert(Hsame:final=ClassSetInput.result native (length(Protocol.classes logical)) value 10 tail) by (rewrite Hrun in Hmodel;congruence).
   rewrite Hsame. unfold ClassSetInput.result. apply allocated_sets.
   + rewrite ClassSetInput.argument_other by discriminate. exact(NativeBasicCommandInvariant.class_count _ _ Hstate).
   + eapply sets_frame;[apply ClassSetInput.argument_other;discriminate|exact Hsets].
   + cbn [fst snd]. rewrite Nat2Z.id. intros;exact HvalueBound.
 - destruct(Nat.eq_dec (Protocol.opcode request) 6%nat) as [H6|H6].
   + destruct request as [opcode values name]. cbn [Protocol.opcode] in H6. subst opcode.
     destruct Hshape as [Hwords [Hlen Hname]]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hlen,Hname,Hargs. subst name.
     destruct values as [|value [|bad values]];cbn [length] in Hlen;try lia.
     inversion Hwords as [|value' values Hvalue Hnil];subst value' values.
   inversion Hargs as [|value' values HvalueBound HnilBound];subst value' values.
     change(meta_value native 15=55) in Hpending.
     rewrite(NativeBasicDispatcher.one_rest 6 value tail ltac:(unfold NativeBasicDispatcher.one;tauto)) in Hinput.
     change(stdin native=32::decimalBytes value++10::tail) in Hinput.
     pose proof(NativeBasicCommandInvariant.formula_count _ _ Hstate) as Hcount.
     destruct(Protocol.formula_at logical value) as [p|] eqn:Hlookup.
     * assert(Hreference:Z.of_nat value<meta_value native 1).
       { unfold Protocol.formula_at in Hlookup. assert(value<length(Protocol.formulas logical))%nat by (apply nth_error_Some;congruence). lia. }
       pose proof(ClassAbstractInput.generated_pending native bs ns (length(Protocol.classes logical)) value 32 10 tail observations
        Hmeta Htoken Hprint Hpending Herror (proj1(NativeState.class_representation _ _ Hstate)) Hroom Hvalue Hreference
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
       assert(Hsame:final=ClassAbstractInput.result native (length(Protocol.classes logical)) value 10 tail) by (rewrite Hrun in Hmodel;congruence).
       rewrite Hsame. unfold ClassAbstractInput.result,ClassAbstractInput.argument_state. apply allocated_sets.
       -- rewrite ReadOne.argument_other by discriminate. exact(NativeBasicCommandInvariant.class_count _ _ Hstate).
       -- eapply sets_frame;[apply ReadOne.argument_other;discriminate|exact Hsets].
       -- cbn [fst snd]. discriminate.
     * assert(Hreference:meta_value native 1<=Z.of_nat value).
       { unfold Protocol.formula_at in Hlookup. apply nth_error_None in Hlookup. lia. }
       pose proof(ClassAbstractInput.generated_rejected native bs ns value 32 10 tail observations
        Hmeta Htoken Hprint Hpending Herror Hvalue Hreference
        ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto) Hinput) as Hmodel.
       assert(Hsame:final=ClassAbstractInput.rejected native value 10 tail) by (rewrite Hrun in Hmodel;congruence).
       assert(Hraw:memory final arraydef_0__classes=memory native arraydef_0__classes).
       { rewrite Hsame. change(memory(ClassAbstractInput.argument_state native value 10 tail) arraydef_0__classes=memory native arraydef_0__classes).
         unfold ClassAbstractInput.argument_state. apply ReadOne.argument_other;discriminate. }
       eapply sets_frame;[exact Hraw|exact Hsets].
   + assert(Hraw:memory final arraydef_0__classes=memory native arraydef_0__classes).
     { eapply NativeBasicCommandInvariant.request_array;try eassumption.
       - unfold NativeBasicInvariant.Arrays.kind;tauto.
       - unfold NativeBasicInvariant.Arrays.unchanged;intuition congruence. }
     eapply sets_frame;[exact Hraw|exact Hsets].
Qed.

Theorem preserves native logical request bs ns tail observations final trace reply next source_bound target_bound :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> NativeBasicDispatcher.resources native logical request ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)source_bound ->
 (source_bound<=target_bound)%nat -> Forall(fun value=>(value<=target_bound)%nat)(Protocol.arguments request) ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 SchemaEvaluationIndexCell.bounded final(Protocol.formulas next)(Protocol.classes next)target_bound.
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Htop Hfalse Hgood Hunique
   [Hraw Hclasses] Hle Hargs Hinput Hrun Hstep Hnext.
 pose proof(NativeBasicCommandInvariant.preserves native logical request bs ns tail observations final trace reply next
 Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Htop Hfalse Hgood Hunique Hinput Hrun Hstep Hnext)
 as(HnextTop & HnextFalse & HnextGood & Hrest).
 pose proof(Bounds.raw_arena_mono native(length(Protocol.formulas logical))source_bound target_bound Hle Hraw) as HrawTarget.
 assert(Hsets:set_indices native target_bound).
 { eapply set_indices_mono;[exact Hle|]. eapply source_set_indices;[exact(NativeState.class_representation _ _ Hstate)|exact Hclasses]. }
 apply bounded_final;[exact Hnext|exact HnextTop| |].
 - exact(raw_preserves native logical request bs ns tail observations final trace next target_bound Hshape Hsupported Hmeta Htoken Hprint
    Hpending Herror (NativeBasicDispatcher.formula_room _ _ _ Hresources) (NativeBasicDispatcher.history_room _ _ _ Hresources)
    Hstate Hnext (NativeBasicDispatcher.safe_history _ Hsafe) Htop HrawTarget Hargs Hinput Hrun).
 - exact(sets_preserves native logical request bs ns tail observations final trace next target_bound Hshape Hsupported Hmeta Htoken Hprint
    Hpending Herror (NativeBasicDispatcher.class_room _ _ _ Hresources) Hargs Hinput Hrun Hstate Hnext Hsets).
Qed.
Fixpoint arguments_max values := match values with []=>0%nat|head::rest=>Nat.max head(arguments_max rest) end.
Lemma arguments_bounded values : Forall(fun value=>(value<=arguments_max values)%nat)values.
Proof.
 induction values as [|value rest IH];[constructor|]. cbn [arguments_max]. constructor;[apply Nat.le_max_l|].
 eapply Forall_impl;[exact IH|]. intros item Hitem. eapply Nat.le_trans;[exact Hitem|apply Nat.le_max_r].
Qed.
Theorem preserves_max native logical request bs ns tail observations final trace reply next bound :
 Protocol.shape request -> NativeBasicDispatcher.supported(Protocol.opcode request) ->
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical -> NativeBasicDispatcher.resources native logical request ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)bound ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 Protocol.step logical request reply next -> NativeState.represents final next ->
 SchemaEvaluationIndexCell.bounded final(Protocol.formulas next)(Protocol.classes next)(Nat.max bound(arguments_max(Protocol.arguments request))).
Proof.
 intros Hshape Hsupported Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hresources Htop Hfalse Hgood Hunique Hbounded Hinput Hrun Hstep Hnext.
 eapply preserves;try eassumption.
 - apply Nat.le_max_l.
 - eapply Forall_impl;[apply arguments_bounded|]. intros value Hvalue.
   eapply Nat.le_trans;[exact Hvalue|apply Nat.le_max_r].
Qed.
End NativeBasicIndexInvariant.
