From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFour AxiomCommand AxiomRefl AxiomStorage AxiomK AxiomFixedCircuits AxiomFixedRefinement AxiomReflProtocol FormulaTopology
  ArenaFrame Representation ClassStorage HistoryRefinement HistoryStorage SemanticFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomFixedProtocol.
Import IndexExecution SipHashExecution.
Definition tag which := Z.to_nat (AxiomFixedCircuits.selector which).
Lemma tag_value which : Z.of_nat (tag which)=AxiomFixedCircuits.selector which.
Proof. destruct which;reflexivity. Qed.
Lemma request_meaning logical which a b c :
  Protocol.concrete_axiom logical (tag which) a b c=Some (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)).
Proof. destruct which;reflexivity. Qed.
Theorem generated_fixed which s logical bs ns ch chars a b c sep0 sep1 sep2 sep3 sep4 tail observations :
  decimalBytes 11=ch::chars ->
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (length (Protocol.formulas logical)+length (AxiomFixedCircuits.plan which))<=9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical))<maximum ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  stdin s=chars++sep0::decimalBytes (tag which)++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index) /\
    nth_error fs index=Some (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) /\ SetTheory.derives (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (AxiomReflProtocol.logical_after logical fs index) /\
    (Guarantees.safe logical -> Guarantees.safe (AxiomReflProtocol.logical_after logical fs index)).
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbudget Hhistorybound Ha Hb Hc
    Harena Hclasses Hhistory Hordered Hfalse Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  assert (Hcode:Z.of_nat 11<=maximum) by (unfold maximum;lia).
  assert (Htag:Z.of_nat (tag which)<=maximum) by (destruct which;unfold tag,AxiomFixedCircuits.selector,maximum;cbn;lia).
  destruct (ReadFour.generated_reads s 11 ch chars (tag which) a b c sep0 sep1 sep2 sep3 sep4 tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFour.fourth_state s ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail).
  pose proof Hfourth as [_ [Hargmeta [_ [_ Hargerror]]]].
  change (17<length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (meta_value arg 8=0) in Hargerror.
  change (20<=length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  assert (Harg_arena:NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { eapply ArenaFrame.storage_arena;[apply ReadFour.fourth_storage;exact Hmeta|exact Harena]. }
  pose proof (AxiomReflProtocol.argument_history s logical ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail Hmeta Hhistory) as Harg_history.
  pose proof (AxiomReflProtocol.argument_classes s (Protocol.formulas logical) (Protocol.classes logical) ch chars (tag which) sep1 a sep2 b sep3 c sep4 tail Hmeta Hclasses) as Harg_classes.
  assert (Harg_ordered:FormulaTopology.ordered arg (length (Protocol.formulas logical))).
  { eapply AxiomK.storage_topology;[apply ReadFour.fourth_storage;exact Hmeta|exact Hordered]. }
  destruct (AxiomFixedRefinement.generated_refines which arg (fun _=>false)
    (AxiomCommand.arguments (Z.of_nat (tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    (Protocol.formulas logical) 0 observations Harg_arena Harg_ordered Hargerror ltac:(lia) Hfalse
    ltac:(now rewrite Nat.add_0_r) (tag_value which))
    as (built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hstorage & Hremaining & Htopology & Hgrowth).
  pose proof (AxiomStorage.history_transport arg built logical Hstorage Harg_history) as Hbuilt_history.
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta:(17<length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest];lia).
  assert (Hpostbuffer:(20<=length (memory built arraydef_0__printBuffer))%nat) by
    (rewrite Harrays by discriminate;exact Hargbuffer).
  pose proof (AxiomCommand.generated_command s bs ns _ _ _ _ arg built (Z.of_nat (tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)
    (length (Protocol.history logical)) index true observations Hopcode Hfirst Hsecond Hthird Hfourth Hhelper
    Hpostmeta Hsuccess Hflag Hindex (proj1 Hbuilt_history) Hhistorybound Hpostbuffer) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput_helper,Houtput_helper,Hinput,Houtput in Hrun.
  assert (Hunique:NoDup fs) by (eapply SemanticFrames.arena_NoDup;exact Hnext).
  assert (Hstep:Protocol.step logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index)).
  { eapply Protocol.step_accept with (t:=AxiomReflProtocol.logical_after logical fs index).
    - unfold AxiomReflProtocol.logical_after,AxiomReflProtocol.before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) fs (Protocol.classes logical) index).
      + apply Protocol.req_axiom. apply request_meaning.
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
End AxiomFixedProtocol.
