From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFour AxiomCommand AxiomRefl AxiomStorage AxiomK
  AxiomInstRefinement AxiomDistRefinement AxiomSeparationRefinement AxiomReplacementRefinement AxiomReflProtocol FormulaTopology
  RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition
  ArenaFrame Representation ClassStorage HistoryRefinement HistoryStorage SemanticFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomRenamingProtocol.
Import IndexExecution SipHashExecution.
Inductive kind := inst | dist | separation | replacement.
Definition tag which : nat := match which with inst=>3|dist=>4|separation=>15|replacement=>16 end.
Definition witness which p q b := match which with inst=>SetTheory.Inst p b|dist=>SetTheory.Dist p q|separation=>SetTheory.Separation p|replacement=>SetTheory.Replacement p end.
Definition expected which p q b := SetTheory.axiom_formula (witness which p q b).
Definition bindings which (fs:list SetTheory.formula) a b p q := nth_error fs a=Some p /\ match which with dist=>nth_error fs b=Some q|_=>True end.
Definition cost which a := match which with inst=>(S a*S a+2)%nat|dist=>(S a*S a+5)%nat|separation=>(S a*S a+14)%nat|replacement=>(3*(S a*S a)+21)%nat end.
Definition increment which b : nat := match which with inst=>b|dist=>1|_=>2 end.
Lemma request_meaning logical which a b c p q : bindings which (Protocol.formulas logical) a b p q ->
  Protocol.concrete_axiom logical (tag which) a b c=Some (expected which p q b).
Proof.
  destruct which;intros [Hp Hq];unfold Protocol.concrete_axiom,Protocol.formula_at;cbn;rewrite Hp;try rewrite Hq;reflexivity.
Qed.
Definition constructed s bs ns observations fs wanted := exists final next index,
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
  NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
  nth_error next index=Some wanted /\ SetTheory.derives wanted /\ (exists extra,next=fs++extra) /\
  meta_value final 8=0 /\ meta_value final 13=1 /\ AxiomStorage.logical_frame s final.
Lemma normalize s bs ns observations fs wanted final next :
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) ->
  NativeRepresentation.canonical_arena final next -> meta_value final 13=1 -> meta_value final 8=0 ->
  word (meta_value final 0) -> nth_error next (Z.to_nat (meta_value final 0))=Some wanted -> SetTheory.derives wanted ->
  (exists extra,next=fs++extra) -> constructed s bs ns observations fs wanted.
Proof.
  intros Hrun Hnext Hsuccess Herror Hword Hmeaning Hderives Hprefix.
  pose proof (AxiomStorage.generated_frame _ _ _ _ _ _ Hrun) as Hframe.
  exists final,next,(Z.to_nat (meta_value final 0)). rewrite Z2Nat.id by exact (proj1 Hword).
  repeat first [assumption|split].
Qed.
Lemma construct which s fs a b c p q bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs 0=Some SetTheory.falsity -> bindings which fs a b p q ->
  Z.of_nat (RenameMemoBounds.fuel a)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+Z.of_nat (increment which b)<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+cost which a)<=9223372036854775807 ->
  constructed s (fun _=>false) (AxiomCommand.arguments (Z.of_nat (tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    observations fs (expected which p q b).
Proof.
  intros Hmeta Hsip Harena Hordered Herror Hfalse [Hp Hq] Hfuel Hbound Hindices Hheight Hbudget.
  destruct which.
  - destruct (AxiomInstRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 3 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a b bound 0 observations Hmeta Hsip Harena Hordered Herror Hp Hfalse eq_refl eq_refl eq_refl
      Hfuel Hbound Hindices Hheight ltac:(cbn [cost] in Hbudget;lia))
      as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hreserve & Htopology & Hgrowth).
    exists final,next,index. repeat first [assumption|split].
  - destruct (AxiomDistRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 4 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p q a b bound 0 observations Hmeta Hsip Harena Hordered Herror Hp Hq Hfalse eq_refl eq_refl eq_refl
      Hfuel Hbound Hindices Hheight ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct (AxiomSeparationRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 15 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a bound 0 observations Hmeta Hsip Harena Hordered Herror Hp Hfalse eq_refl eq_refl
      Hfuel Hbound Hindices Hheight ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct (AxiomReplacementRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 16 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
      fs p a bound 0 observations Hmeta Hsip Harena Hordered Herror Hp Hfalse eq_refl eq_refl
      Hfuel Hbound Hindices Hheight ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    eapply normalize;eassumption.
Qed.

Theorem generated_renaming which s logical bs ns ch chars a b c p q bound sep0 sep1 sep2 sep3 sep4 tail observations :
  decimalBytes 11=ch::chars ->
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (length (Protocol.formulas logical)+cost which a)<=9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical))<maximum ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  bindings which (Protocol.formulas logical) a b p q ->
  Z.of_nat (RenameMemoBounds.fuel a)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+Z.of_nat (increment which b)<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  stdin s=chars++sep0::decimalBytes (tag which)++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index) /\
    nth_error fs index=Some (expected which p q b) /\ SetTheory.derives (expected which p q b) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (AxiomReflProtocol.logical_after logical fs index) /\
    (Guarantees.safe logical -> Guarantees.safe (AxiomReflProtocol.logical_after logical fs index)).
Proof.
  intros Hencoding Hmeta Hsip Htoken Hbuffer Hpending Herror Hbudget Hhistorybound Ha Hb Hc
    Harena Hclasses Hhistory Hordered Hfalse Hbindings Hfuel Hbound Hindices Hheight Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  assert (Hcode:Z.of_nat 11<=maximum) by (unfold maximum;lia).
  assert (Htag:Z.of_nat (tag which)<=maximum) by (destruct which;unfold tag,maximum;lia).
  destruct (ReadFour.generated_reads s 11 ch chars (tag which) a b c sep0 sep1 sep2 sep3 sep4 tail observations
    ltac:(lia) Htoken Hbuffer Hpending Herror Hcode Hencoding Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFour.fourth_state s ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail).
  pose proof Hfourth as [_ [Hargmeta [_ [_ Hargerror]]]].
  change (17<length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (meta_value arg 8=0) in Hargerror.
  change (20<=length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  assert (Harg_arena:NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { eapply ArenaFrame.storage_arena;[apply ReadFour.fourth_storage;lia|exact Harena]. }
  pose proof (AxiomReflProtocol.argument_history s logical ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail ltac:(lia) Hhistory) as Harg_history.
  pose proof (AxiomReflProtocol.argument_classes s (Protocol.formulas logical) (Protocol.classes logical) ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail ltac:(lia) Hclasses) as Harg_classes.
  assert (Harg_ordered:FormulaTopology.ordered arg (length (Protocol.formulas logical))).
  { eapply AxiomK.storage_topology;[apply ReadFour.fourth_storage;lia|exact Hordered]. }
  assert (Hargmeta32:(31<length (memory arg arraydef_0__meta))%nat).
  { unfold arg. rewrite ReadFour.fourth_meta_length. exact Hmeta. }
  assert (Hargsip:(0<length (memory arg arraydef_0__sipState))%nat).
  { unfold arg. rewrite ReadFour.fourth_other by discriminate. exact Hsip. }
  destruct (construct which arg (Protocol.formulas logical) a b c p q bound observations
    Hargmeta32 Hargsip Harg_arena Harg_ordered Hargerror Hfalse Hbindings Hfuel Hbound Hindices Hheight Hbudget)
    as (built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderives & Hprefix & Hflag & Hsuccess & Hframe).
  pose proof (AxiomStorage.generated_frame _ _ _ _ _ _ Hhelper) as Hstorage.
  pose proof (AxiomStorage.history_transport arg built logical Hstorage Harg_history) as Hbuilt_history.
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta:(17<length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest];lia).
  assert (Hpostbuffer:(20<=length (memory built arraydef_0__printBuffer))%nat) by
    (rewrite Harrays by (repeat split;discriminate);exact Hargbuffer).
  pose proof (AxiomCommand.generated_command s bs ns _ _ _ _ arg built (Z.of_nat (tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)
    (length (Protocol.history logical)) index true observations Hopcode Hfirst Hsecond Hthird Hfourth Hhelper
    Hpostmeta Hsuccess Hflag Hindex (proj1 Hbuilt_history) Hhistorybound Hpostbuffer) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput_helper,Houtput_helper,Hinput,Houtput in Hrun.
  assert (Hunique:NoDup fs) by (eapply SemanticFrames.arena_NoDup;exact Hnext).
  assert (Hstep:Protocol.step logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index)).
  { eapply Protocol.step_accept with (t:=AxiomReflProtocol.logical_after logical fs index).
    - unfold AxiomReflProtocol.logical_after,AxiomReflProtocol.before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (expected which p q b) fs (Protocol.classes logical) index).
      + apply Protocol.req_axiom. now apply request_meaning.
      + split;[exact Hprefix|]. split;[exact Hunique|]. split;[exact Hformula|]. exists [];now rewrite app_nil_r.
    - apply HistoryRefinement.retained_refl. exact Hunique. }
  exists (HistoryStorage.result built (length (Protocol.history logical)) (Z.of_nat index)),index,fs.
  split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hformula|]. split;[exact Hderives|].
  split;[now apply HistoryStorage.result_arena|]. split.
  - apply HistoryStorage.result_classes. destruct Hprefix as [extra ->]. eapply AxiomStorage.classes_transport;eassumption.
  - split.
    + apply (HistoryStorage.append_represents built (AxiomReflProtocol.before_append logical fs) index ltac:(lia) Hbuilt_history).
    + intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End AxiomRenamingProtocol.
