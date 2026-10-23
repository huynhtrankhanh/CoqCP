From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFour AxiomCommand AxiomRefl AxiomStorage AxiomK
  AxiomSRefinement AxiomDNERefinement AxiomEqualityCircuits AxiomEqualityRefinement AxiomReflProtocol FormulaTopology
  ArenaFrame Representation ClassStorage HistoryRefinement HistoryStorage SemanticFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomLogicalProtocol.
Import IndexExecution SipHashExecution.
Inductive kind := k | srule | dne | equality (which:AxiomEqualityCircuits.kind).
Definition tag which : nat := match which with k=>0 | srule=>1 | dne=>2 | equality w=>Z.to_nat (AxiomEqualityCircuits.selector w) end.
Definition witness which p q r a b c := match which with
| k=>SetTheory.K p q | srule=>SetTheory.Srule p q r | dne=>SetTheory.DNE p
| equality w=>AxiomEqualityCircuits.witness w a b c end.
Definition expected which p q r a b c := SetTheory.axiom_formula (witness which p q r a b c).
Definition bindings which (fs:list SetTheory.formula) a b c p q r := match which with
| k=>nth_error fs a=Some p /\ nth_error fs b=Some q
| srule=>nth_error fs a=Some p /\ nth_error fs b=Some q /\ nth_error fs c=Some r
| dne=>nth_error fs a=Some p
| equality _=>True end.
Definition cost which : nat := match which with k=>2|srule=>6|dne=>3|equality _=>5 end.
Lemma request_meaning logical which a b c p q r : bindings which (Protocol.formulas logical) a b c p q r ->
  Protocol.concrete_axiom logical (tag which) a b c=Some (expected which p q r a b c).
Proof.
  destruct which as [ | | |which].
  - intros [Hp Hq]. unfold Protocol.concrete_axiom,Protocol.formula_at. cbn. rewrite Hp,Hq. reflexivity.
  - intros [Hp [Hq Hr]]. unfold Protocol.concrete_axiom,Protocol.formula_at. cbn. rewrite Hp,Hq,Hr. reflexivity.
  - intro Hp. unfold Protocol.concrete_axiom,Protocol.formula_at. cbn. rewrite Hp. reflexivity.
  - destruct which;reflexivity.
Qed.
Definition constructed s bs ns observations fs wanted := exists final next index,
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
  NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
  nth_error next index=Some wanted /\ SetTheory.derives wanted /\ (exists extra,next=fs++extra) /\
  meta_value final 8=0 /\ meta_value final 13=1 /\ AxiomRefl.logical_frame s final.
Lemma normalize s bs ns observations fs wanted final next :
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) ->
  NativeRepresentation.canonical_arena final next -> meta_value final 13=1 -> meta_value final 8=0 ->
  word (meta_value final 0) -> nth_error next (Z.to_nat (meta_value final 0))=Some wanted -> SetTheory.derives wanted ->
  (exists extra,next=fs++extra) -> AxiomRefl.logical_frame s final -> constructed s bs ns observations fs wanted.
Proof.
  intros Hrun Hnext Hsuccess Herror Hword Hmeaning Hderives Hprefix Hframe.
  exists final,next,(Z.to_nat (meta_value final 0)). rewrite Z2Nat.id by exact (proj1 Hword).
  repeat first [assumption|split].
Qed.
Lemma construct which s fs a b c p q r observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  word (Z.of_nat a) -> word (Z.of_nat b) -> word (Z.of_nat c) -> bindings which fs a b c p q r ->
  Z.of_nat (length fs+cost which)<=9223372036854775807 ->
  constructed s (fun _=>false) (AxiomCommand.arguments (Z.of_nat (tag which)) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c))
    observations fs (expected which p q r a b c).
Proof.
  intros Harena Hordered Herror Hmeta Hfalse Ha Hb Hc Hbindings Hbudget.
  destruct which as [ | | |which].
  - destruct Hbindings as [Hp Hq].
    destruct (AxiomK.generated_refines s (fun _=>false) (AxiomCommand.arguments 0 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) (Z.of_nat b) p q 0 observations Harena Hordered Herror Hmeta eq_refl eq_refl eq_refl Ha Hb
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct Hbindings as [Hp [Hq Hr]].
    destruct (AxiomSRefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 1 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) p q r 0 observations Harena Hordered Herror Hmeta eq_refl eq_refl eq_refl eq_refl Ha Hb Hc
      ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) ltac:(now rewrite Nat2Z.id) ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    eapply normalize;eassumption.
  - destruct (AxiomDNERefinement.generated_refines s (fun _=>false) (AxiomCommand.arguments 2 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs
      (Z.of_nat a) p 0 observations Harena Hordered Herror Hmeta Hfalse Ha ltac:(now rewrite Nat2Z.id)
      ltac:(cbn [cost] in Hbudget;lia) eq_refl eq_refl)
      as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hframe & Hreserve & Htopology & Hgrowth).
    exists final,next,index. repeat first [assumption|split].
  - destruct (AxiomEqualityRefinement.generated_refines which s (fun _=>false)
      (AxiomCommand.arguments (AxiomEqualityCircuits.selector which) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) fs a b c 0 observations
      Harena Hordered Herror Hmeta eq_refl eq_refl eq_refl eq_refl Ha Hb Hc ltac:(cbn [cost] in Hbudget;lia))
      as (built & next & Hrun & Hnext & Hsuccess & Hflag & Hword & Hmeaning & Hderives & Hprefix & Hreserve & Htopology & Hgrowth & Hframe).
    destruct which;eapply normalize;eassumption.
Qed.

Theorem generated_logical which s logical bs ns ch chars a b c p q r sep0 sep1 sep2 sep3 sep4 tail observations :
  decimalBytes 11=ch::chars ->
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (length (Protocol.formulas logical)+cost which)<=9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical))<maximum ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> HistoryRefinement.represents s logical ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  bindings which (Protocol.formulas logical) a b c p q r ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  stdin s=chars++sep0::decimalBytes (tag which)++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
  exists final index fs,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index) /\
    nth_error fs index=Some (expected which p q r a b c) /\ SetTheory.derives (expected which p q r a b c) /\
    NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs (Protocol.classes logical) /\
    HistoryRefinement.represents final (AxiomReflProtocol.logical_after logical fs index) /\
    (Guarantees.safe logical -> Guarantees.safe (AxiomReflProtocol.logical_after logical fs index)).
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hbudget Hhistorybound Ha Hb Hc
    Harena Hclasses Hhistory Hordered Hfalse Hbindings Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  assert (Hcode:Z.of_nat 11<=maximum) by (unfold maximum;lia).
  assert (Htag:Z.of_nat (tag which)<=maximum) by (destruct which as [ | | |which];[unfold tag,maximum;lia|unfold tag,maximum;lia|unfold tag,maximum;lia|destruct which;unfold tag,AxiomEqualityCircuits.selector,maximum;cbn;lia]).
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
  assert (Haword:word (Z.of_nat a)) by (unfold word;lia).
  assert (Hbword:word (Z.of_nat b)) by (unfold word;lia).
  assert (Hcword:word (Z.of_nat c)) by (unfold word;lia).
  destruct (construct which arg (Protocol.formulas logical) a b c p q r observations
    Harg_arena Harg_ordered Hargerror ltac:(lia) Hfalse Haword Hbword Hcword Hbindings Hbudget)
    as (built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderives & Hprefix & Hflag & Hsuccess & Hframe).
  pose proof (AxiomStorage.generated_frame _ _ _ _ _ _ Hhelper) as Hstorage.
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
      eapply (Protocol.accept_proof logical (Protocol.Req 11 [tag which;a;b;c]%nat []) (expected which p q r a b c) fs (Protocol.classes logical) index).
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
End AxiomLogicalProtocol.
