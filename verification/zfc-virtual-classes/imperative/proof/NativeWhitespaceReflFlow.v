From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFour AxiomCommand AxiomRefl AxiomStorage
  ArenaFrame Representation ClassStorage HistoryRefinement HistoryStorage SemanticFrames ReplyOK NativeArgumentReadsFour NativeTheoremBoundary NativeProtocolLift NativeState NativeStateFrames NativeCommandBoundary NativeWhitespaceGeneralizeBoundary NativeWhitespaceReflBoundary AxiomReflProtocol.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceReflFlow.
Import IndexExecution SipHashExecution.
Definition before_append logical fs := Protocol.State fs (Protocol.classes logical) (Protocol.history logical)
  (Protocol.bindings logical) (Protocol.expressions logical).
Definition logical_after logical fs index := Protocol.with_history (before_append logical fs) (Protocol.history logical++[index]).
Import NativeTheoremBoundary NativeWhitespaceReflBoundary.
Lemma read_four_frame native ch chars tag sep1 variable sep2 b sep3 c sep4 tail :
 (17<length(memory native arraydef_0__meta))%nat ->
 stdin(ReadFour.fourth_state native ch chars tag sep1 variable sep2 b sep3 c sep4 tail)=tail ->
 stdout(ReadFour.fourth_state native ch chars tag sep1 variable sep2 b sep3 c sep4 tail)=stdout native ->
 frame native (ReadFour.fourth_state native ch chars tag sep1 variable sep2 b sep3 c sep4 tail) tail.
Proof. intros Hmeta Hin Hout. split;[exact Hin|]. split;[exact Hout|]. intros;apply ReadFour.fourth_meta_other;assumption. Qed.
Lemma refl_history_flow before parsed built fs next count fid tail :
 frame before parsed tail -> AxiomRefl.logical_frame parsed built ->
 NativeRepresentation.canonical_arena parsed fs -> NativeRepresentation.canonical_arena built next ->
 (length next<=S (length fs))%nat -> meta_value built 8=0 ->
 (3<length (memory built arraydef_0__meta))%nat -> meta_value built 3=Z.of_nat count ->
 flow 1 before (HistoryStorage.result built count fid) (Protocol.OK count) tail.
Proof.
 intros [Hin [Hout Hparse]] [Harrays [Hcells [Hinput Houtput]]] Harena Hnext Hgrowth Herror Hmeta Hcount.
 assert (H1:meta_value parsed 1=meta_value before 1) by (apply Hparse;lia).
 assert (H2:meta_value built 2=meta_value before 2).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 assert (H3:meta_value built 3=meta_value before 3).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 assert (H9:meta_value built 9=meta_value before 9).
 { etransitivity;[apply Hcells;lia|apply Hparse;lia]. }
 pose proof (proj1 (proj2 (proj1 Harena))) as HbeforeCount.
 pose proof (proj1 (proj2 (proj1 Hnext))) as HnextCount.
 change (meta_value parsed 1=Z.of_nat (length fs)) in HbeforeCount.
 change (meta_value built 1=Z.of_nat (length next)) in HnextCount.
 assert (Hformula:meta_value built 1<=meta_value before 1+1).
 { apply Nat2Z.inj_le in Hgrowth. rewrite Nat2Z.inj_succ in Hgrowth. lia. }
 unfold flow. split.
 - change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written built count fid) count)=tail).
   exact (eq_trans (ReplyOKExecution.reply_input (HistoryStorage.written built count fid) count) (eq_trans Hinput Hin)).
 - split.
   + change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written built count fid) count)=stdout before++Protocol.reply_bytes (Protocol.OK count)).
     exact (eq_trans (ReplyOKExecution.reply_output (HistoryStorage.written built count fid) count)
       (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK count)) (eq_trans Houtput Hout))).
   + split;[rewrite HistoryStorage.result_meta_other by lia;exact Herror|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact H9|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact Hformula|].
     split;[rewrite HistoryStorage.result_meta_other by lia;exact H2|].
     rewrite HistoryStorage.result_count by exact Hmeta. rewrite Nat2Z.inj_succ;lia.
Qed.
Theorem generated_reflexivity s logical bs ns ch chars variable b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations :
  decimalBytes 11=ch::chars ->
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (length (Protocol.formulas logical)+1)<=9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical))<maximum ->
  Z.of_nat variable<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 -> Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
  stdin s=chars++sep0::sp1++decimalBytes 5++sep1::sp2++decimalBytes variable++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++sep4::tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index) /\
    nth_error fs index=Some (SetTheory.equal variable variable) /\ SetTheory.derives (SetTheory.equal variable variable) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (logical_after logical fs index) /\
    (Guarantees.safe logical -> Guarantees.safe (logical_after logical fs index)) /\ flow 1 s final (Protocol.OK (length (Protocol.history logical))) tail.
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbudget Hhistorybound Hvariable Hb Hc
    Harena Hclasses Hhistory Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hin.
  assert (Hcode:Z.of_nat 11<=maximum) by (unfold maximum;lia).
  assert (Htag:Z.of_nat 5<=maximum) by (unfold maximum;lia).
  destruct (NativeArgumentReadsFour.generated_reads s 11 ch chars 5 variable b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Htag Hvariable Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFour.fourth_state s ch chars 5 sep1 variable sep2 b sep3 c sep4 tail).
  pose proof Hfourth as [_ [Hargmeta [_ [_ Hargerror]]]].
  change (17<length (memory arg arraydef_0__meta))%nat in Hargmeta.
  change (meta_value arg 8=0) in Hargerror.
  change (20<=length (memory arg arraydef_0__printBuffer))%nat in Hargbuffer.
  assert (Harg_arena:NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
  { eapply ArenaFrame.storage_arena;[apply ReadFour.fourth_storage;exact Hmeta|exact Harena]. }
  pose proof (argument_history s logical ch chars 5 sep1 variable sep2 b sep3 c sep4 tail Hmeta Hhistory) as Harg_history.
  pose proof (argument_classes s (Protocol.formulas logical) (Protocol.classes logical) ch chars 5 sep1 variable sep2 b sep3 c sep4 tail Hmeta Hclasses) as Harg_classes.
  assert (Hvariableword:word (Z.of_nat variable)) by (unfold word;lia).
  set(reserve:=Z.to_nat(9223372036854775807-Z.of_nat(length(Protocol.formulas logical))-1)).
  assert(Hreserve:Z.of_nat(length(Protocol.formulas logical)+S reserve)<=9223372036854775807).
  { unfold reserve. rewrite Nat2Z.inj_add,Nat2Z.inj_succ,Z2Nat.id by (rewrite Nat2Z.inj_add in Hbudget;cbn in Hbudget;lia). lia. }
  destruct (AxiomRefl.generated_refines arg (fun _=>false)
    (AxiomCommand.arguments 5 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c)) (Protocol.formulas logical) variable reserve observations
    Harg_arena Hargerror ltac:(lia) Hvariableword Hreserve eq_refl eq_refl)
    as (built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hremaining).
  assert(Hgrowth:(length fs<=S(length(Protocol.formulas logical)))%nat).
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ. unfold reserve in Hremaining.
    rewrite Nat2Z.inj_add,Z2Nat.id in Hremaining by (rewrite Nat2Z.inj_add in Hbudget;cbn in Hbudget;lia). lia. }
  pose proof (AxiomStorage.generated_frame _ _ _ _ _ _ Hhelper) as Hstorage.
  pose proof (AxiomStorage.history_transport arg built logical Hstorage Harg_history) as Hbuilt_history.
  pose proof Hframe as [Harrays [Hcells [Hinput_helper Houtput_helper]]].
  assert (Hpostmeta:(17<length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 Hnext)) as [Hcapacity Hrest];lia).
  assert (Hpostbuffer:(20<=length (memory built arraydef_0__printBuffer))%nat) by
    (rewrite Harrays by discriminate;exact Hargbuffer).
  pose proof (AxiomCommand.generated_command s bs ns _ _ _ _ arg built 5 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c)
    (length (Protocol.history logical)) index true observations Hopcode Hfirst Hsecond Hthird Hfourth Hhelper
    Hpostmeta Hsuccess Hflag Hindex (proj1 Hbuilt_history) Hhistorybound Hpostbuffer) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput_helper,Houtput_helper,Hinput,Houtput in Hrun.
  assert (Hunique:NoDup fs) by (eapply SemanticFrames.arena_NoDup;exact Hnext).
  assert (Hstep:Protocol.step logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (logical_after logical fs index)).
  { eapply Protocol.step_accept with (t:=logical_after logical fs index).
    - unfold logical_after,before_append. cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
      eapply (Protocol.accept_proof logical (Protocol.Req 11 [5;variable;b;c]%nat []) (SetTheory.equal variable variable) fs (Protocol.classes logical) index).
      + apply Protocol.req_axiom. reflexivity.
      + split;[exact Hprefix|]. split;[exact Hunique|]. split;[exact Hformula|]. exists [];now rewrite app_nil_r.
    - apply HistoryRefinement.retained_refl. exact Hunique. }
  exists (HistoryStorage.result built (length (Protocol.history logical)) (Z.of_nat index)),index,fs.
  split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hformula|]. split;[exact Hderives|].
  split;[now apply HistoryStorage.result_arena|]. split.
  - apply HistoryStorage.result_classes. destruct Hprefix as [extra ->]. eapply AxiomStorage.classes_transport;eassumption.
  - split.
    + apply (HistoryStorage.append_represents built (before_append logical fs) index ltac:(lia) Hbuilt_history).
    + split.
      * intro Hsafe. eapply Guarantees.step_safe;eassumption.
      * apply (refl_history_flow s arg built (Protocol.formulas logical) fs (length(Protocol.history logical)) (Z.of_nat index) tail
          (read_four_frame s ch chars 5 sep1 variable sep2 b sep3 c sep4 tail Hmeta Hinput Houtput) Hframe Harg_arena Hnext Hgrowth Hflag ltac:(lia) (proj1 Hbuilt_history)).
Qed.
Theorem generated s logical bs ns ch chars variable b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations :
 decimalBytes 11=ch::chars ->
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 (20<=length(memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat(length(Protocol.formulas logical)+1)<=9223372036854775807 -> Z.of_nat(length(Protocol.history logical))<maximum ->
 Z.of_nat variable<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> NativeState.represents s logical ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 -> TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 -> Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
 stdin s=chars++sep0::sp1++decimalBytes 5++sep1::sp2++decimalBytes variable++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++sep4::tail ->
 exists final index fs,
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes(Protocol.OK(length(Protocol.history logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK(length(Protocol.history logical))) (logical_after logical fs index) /\
 NativeState.represents final (logical_after logical fs index) /\ boundary 1 s logical final (Protocol.OK(length(Protocol.history logical))) (logical_after logical fs index) tail.
Proof.
 intros Hencoding Hmeta Htoken Hprint Hpending Herror Hbudget Hhistory Hvariable Hb Hc Hstate Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hinput.
 destruct(generated_reflexivity s logical bs ns ch chars variable b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations Hencoding Hmeta Htoken Hprint Hpending Herror Hbudget Hhistory Hvariable Hb Hc
  (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate) (NativeState.history_representation _ _ Hstate)
  Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hinput) as(final & index & fs & Hrun & Hstep & Hformula & Hderives & Harena & Hclasses & Hhist & Hsafe & Hflow).
 assert(Hnext:NativeState.represents final (logical_after logical fs index)).
 { eapply (NativeProtocolLift.canonical 11 ch chars s bs ns sep0 (sp1++decimalBytes 5++sep1::sp2++decimalBytes variable++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++sep4::tail)
  observations final _ logical (Protocol.Req 11 [5;variable;b;c]%nat []) (Protocol.OK(length(Protocol.history logical))) (logical_after logical fs index));try eassumption.
  - change ([49;49]=ch::chars) in Hencoding. inversion Hencoding;subst;lia.
  - unfold NativeStateFrames.nonbinding;repeat split;lia.
  - unfold NativeStateFrames.nonbinding;repeat split;lia.
  - reflexivity. all: try reflexivity. all: try assumption. }
 exists final,index,fs. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|].
 exact(boundary_from_flow 1 s final bs ns logical _ _ tail observations _ Hstate Hnext Htoken Hprint Hrun Hflow).
Qed.
End NativeWhitespaceReflFlow.
