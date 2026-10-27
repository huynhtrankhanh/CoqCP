From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash AxiomTaggedInvariant AxiomInvariant AxiomStorage AxiomCommand AxiomReflProtocol
 AxiomRejectionProtocol NativeState NativeProtocolLift NativeCommandLengths NativeStateFrames ReadFour TokenByte
 Representation ClassStorage ClassLookup FormulaTopology HistoryRefinement HistoryStorage SemanticFrames RenameStorage
 InternalIO ReplyOK ReplyNO ArenaFrame HashTable NativeCommandBoundary AxiomReject.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAxiomTotal.
Import IndexExecution SipHashExecution.
Definition resources logical tag a b c := forall wanted,
 Protocol.concrete_axiom logical tag a b c=Some wanted -> exists p q r bound,
 AxiomTaggedInvariant.ready (Protocol.formulas logical) tag a b c a b c p q r /\
 AxiomTaggedInvariant.renaming_ready tag a b p bound /\
 Z.of_nat (length (Protocol.formulas logical)+AxiomTaggedInvariant.cost tag a)<=9223372036854775807.
Lemma valid_tag logical tag a b c wanted :
 Protocol.concrete_axiom logical tag a b c=Some wanted -> (tag<=17)%nat.
Proof.
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 all:try lia. discriminate.
Qed.
Lemma ready_meaning logical tag a b c p q r : (tag<=17)%nat ->
 AxiomTaggedInvariant.ready (Protocol.formulas logical) tag a b c a b c p q r ->
 option_map SetTheory.axiom_formula (AxiomTaggedInvariant.literal_axiom tag p q r a b c)=Protocol.concrete_axiom logical tag a b c.
Proof.
 intros Htag Hready.
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 19:lia.
 all:destruct Hready as [HA [HB HC]];
   cbn [AxiomTaggedInvariant.needs_p AxiomTaggedInvariant.needs_q existsb Nat.eqb orb] in HA,HB,HC.
 all:unfold Protocol.concrete_axiom,Protocol.formula_at,AxiomTaggedInvariant.literal_axiom;
   cbn [Schemata.instantiate_axiom Schemata.instantiate_formula];
   rewrite ?HA,?HB,?HC;reflexivity.
Qed.
Theorem generated_accepted s logical bs ns ch chars tag a b c wanted p q r bound sep0 sep1 sep2 sep3 sep4 tail observations :
 decimalBytes 11=ch::chars -> Protocol.concrete_axiom logical tag a b c=Some wanted ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat (length (Protocol.history logical))<maximum ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 NativeState.represents s logical -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 AxiomTaggedInvariant.ready (Protocol.formulas logical) tag a b c a b c p q r ->
 AxiomTaggedInvariant.renaming_ready tag a b p bound ->
 Z.of_nat (length (Protocol.formulas logical)+AxiomTaggedInvariant.cost tag a)<=9223372036854775807 ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 stdin s=chars++sep0::decimalBytes tag++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
 exists final index fs,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index) /\
 nth_error fs index=Some wanted /\ SetTheory.derives wanted /\
 NativeState.represents final (AxiomReflProtocol.logical_after logical fs index) /\
 stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical))) /\
 (1024<=length (memory final arraydef_0__token))%nat /\ (20<=length (memory final arraydef_0__printBuffer))%nat /\
 meta_value final 8=0 /\ meta_value final 9=meta_value s 9 /\
 (Guarantees.safe logical -> Guarantees.safe (AxiomReflProtocol.logical_after logical fs index)).
Proof.
 intros Hencoding Hwanted Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Htag Ha Hb Hc
   Hstate Htop Hfalse Hready Hrename Hbudget Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput.
 pose proof (NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof (NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof (NativeState.history_representation _ _ Hstate) as Hhistory.
 assert (HtagBound:(tag<=17)%nat) by (eapply valid_tag;exact Hwanted).
 destruct (ReadFour.generated_reads s 11 ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations
   ltac:(lia) Htoken Hprint Hpending Herror ltac:(unfold maximum;lia) Hencoding Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput)
 as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargprint & HargIn & HargOut).
 set (arg:=ReadFour.fourth_state s ch chars tag sep1 a sep2 b sep3 c sep4 tail).
 assert (HargArena:NativeRepresentation.canonical_arena arg (Protocol.formulas logical)).
 { eapply ArenaFrame.storage_arena;[apply ReadFour.fourth_storage;lia|exact Harena]. }
 assert (HargTop:FormulaTopology.ordered arg (length (Protocol.formulas logical))).
 { apply (FormulaTopology.same s);[exact Htop|]. intros node Hnode.
   unfold HashTableInvariant.tuple_at,arg. now rewrite ReadFour.fourth_other by discriminate. }
 assert (HargError:meta_value arg 8=0) by (unfold arg;rewrite ReadFour.fourth_meta_other by lia;exact Herror).
 assert (HargMeta:(31<length (memory arg arraydef_0__meta))%nat) by (unfold arg;now rewrite ReadFour.fourth_meta_length).
 assert (HargSip:(0<length (memory arg arraydef_0__sipState))%nat) by (unfold arg;now rewrite ReadFour.fourth_other by discriminate).
 destruct (AxiomTaggedInvariant.construct arg (Protocol.formulas logical) tag a b c a b c p q r bound 0 observations
   HtagBound HargMeta HargSip HargArena HargTop HargError Hfalse
   ltac:(unfold word;lia) ltac:(unfold word;lia) ltac:(unfold word;lia) Hready Hrename ltac:(now rewrite Nat.add_0_r))
 as (witness & Hliteral & built & fs & index & Hhelper & Hnext & Hindex & Hword & Hformula & Hderive & Hprefix & Hclear & Hsuccess & HnextTop & Hreserve & Hgrowth & Hstorage & Hlengths).
 assert (HwantedEqual:SetTheory.axiom_formula witness=wanted).
 { pose proof (ready_meaning logical tag a b c p q r HtagBound Hready) as Hmeaning.
   rewrite Hliteral,Hwanted in Hmeaning. now injection Hmeaning. }
 rewrite HwantedEqual in Hformula,Hderive.
 pose proof (AxiomReflProtocol.argument_history s logical ch chars tag sep1 a sep2 b sep3 c sep4 tail ltac:(lia) Hhistory) as HargHistory.
 pose proof (AxiomReflProtocol.argument_classes s (Protocol.formulas logical) (Protocol.classes logical) ch chars tag sep1 a sep2 b sep3 c sep4 tail ltac:(lia) Hclasses) as HargClasses.
 pose proof (AxiomStorage.history_transport arg built logical Hstorage HargHistory) as HbuiltHistory.
 destruct Hstorage as [Harrays [Hcells [HinHelper HoutHelper]]].
 assert (HbuiltMeta:(17<length (memory built arraydef_0__meta))%nat) by (pose proof (proj1 (proj1 (proj1 Hnext)));lia).
 assert (HbuiltPrint:(20<=length (memory built arraydef_0__printBuffer))%nat).
 { rewrite Harrays by (repeat split;discriminate). exact Hargprint. }
 pose proof (AxiomCommand.generated_command s bs ns _ _ _ _ arg built (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)
   (length (Protocol.history logical)) index true observations Hopcode Hfirst Hsecond Hthird Hfourth Hhelper
   HbuiltMeta Hsuccess Hclear Hindex (proj1 HbuiltHistory) HhistoryRoom HbuiltPrint) as Hrun.
 change (stdin arg=tail) in HargIn. change (stdout arg=stdout s) in HargOut.
 rewrite HinHelper,HoutHelper,HargIn,HargOut in Hrun.
 set (final:=HistoryStorage.result built (length (Protocol.history logical)) (Z.of_nat index)).
 assert (Hunique:NoDup fs) by (exact (SemanticFrames.arena_NoDup built fs Hnext)).
 assert (Hstep:Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index)).
 { eapply Protocol.step_accept with (t:=AxiomReflProtocol.logical_after logical fs index).
   - unfold AxiomReflProtocol.logical_after,AxiomReflProtocol.before_append.
     cbn [Protocol.with_history Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
     eapply (Protocol.accept_proof logical (Protocol.Req 11 [tag;a;b;c] []) wanted fs (Protocol.classes logical) index).
     + apply Protocol.req_axiom;exact Hwanted.
     + split;[exact Hprefix|]. split;[exact Hunique|]. split;[exact Hformula|]. exists [];now rewrite app_nil_r.
   - apply HistoryRefinement.retained_refl;exact Hunique. }
 assert (HfinalArena:NativeRepresentation.canonical_arena final fs) by (now apply HistoryStorage.result_arena).
 assert (HfinalClasses:ClassStorage.represents final fs (Protocol.classes logical)).
 { apply HistoryStorage.result_classes. destruct Hprefix as [extra ->].
   exact (AxiomStorage.classes_transport arg built (Protocol.formulas logical) extra (Protocol.classes logical)
     (conj Harrays (conj Hcells (conj HinHelper HoutHelper))) HargClasses). }
 assert (HfinalHistory:HistoryRefinement.represents final (AxiomReflProtocol.logical_after logical fs index)).
 { apply (HistoryStorage.append_represents built (AxiomReflProtocol.before_append logical fs) index ltac:(lia) HbuiltHistory). }
 assert (HfinalState:NativeState.represents final (AxiomReflProtocol.logical_after logical fs index)).
 { exact (NativeProtocolLift.canonical 11 ch chars s bs ns sep0
   (decimalBytes tag++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail)
   observations final _ logical (Protocol.Req 11 [tag;a;b;c] []) (Protocol.OK (length (Protocol.history logical))) (AxiomReflProtocol.logical_after logical fs index)
   ltac:(lia) ltac:(lia) ltac:(unfold NativeStateFrames.nonbinding;repeat split;lia) eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hsep0 Hinput
   Hrun Hstate Hstep HfinalArena HfinalClasses HfinalHistory). }
 assert (HfinalIn:stdin final=tail).
 { unfold final,HistoryStorage.result.
   change (stdin (ReplyOKExecution.reply_state (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))=tail).
   exact (eq_trans (ReplyOKExecution.reply_input (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))
     (eq_trans HinHelper HargIn)). }
 assert (HfinalOut:stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))).
 { unfold final,HistoryStorage.result.
   change (stdout (ReplyOKExecution.reply_state (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))).
   exact (eq_trans (ReplyOKExecution.reply_output (HistoryStorage.written built (length (Protocol.history logical)) (Z.of_nat index)) (length (Protocol.history logical)))
     (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK (length (Protocol.history logical)))) (eq_trans HoutHelper HargOut))). }
 exists final,index,fs. split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hformula|]. split;[exact Hderive|].
 split;[exact HfinalState|]. split;[exact HfinalIn|]. split;[exact HfinalOut|]. split.
 - rewrite (NativeCommandLengths.generated arraydef_0__token s bs ns final observations _ NativeCommandLengths.token_protected Hrun);exact Htoken.
 - split.
   + rewrite (NativeCommandLengths.generated arraydef_0__printBuffer s bs ns final observations _ NativeCommandLengths.printBuffer_protected Hrun);exact Hprint.
   + split.
     * unfold final. rewrite HistoryStorage.result_meta_other by lia;exact Hclear.
     * split.
       -- unfold final. rewrite HistoryStorage.result_meta_other by lia.
          rewrite Hcells by (try (unfold RenameStorage.Cells.protected);lia).
          unfold arg. apply ReadFour.fourth_meta_other;lia.
       -- intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
Theorem generated_total s logical bs ns ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations :
 decimalBytes 11=ch::chars ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> Z.of_nat (length (Protocol.history logical))<maximum ->
 Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
 NativeState.represents s logical -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> resources logical tag a b c ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 stdin s=chars++sep0::decimalBytes tag++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io s final reply tail /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hencoding Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Htag Ha Hb Hc
   Hstate Htop Hfalse Hresources Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput.
 destruct (Protocol.concrete_axiom logical tag a b c) as [wanted|] eqn:Hconcrete.
 - destruct (Hresources wanted Hconcrete) as (p & q & r & bound & Hready & Hrename & Hbudget).
   destruct (generated_accepted s logical bs ns ch chars tag a b c wanted p q r bound sep0 sep1 sep2 sep3 sep4 tail observations
     Hencoding Hconcrete Hmeta Hsip Htoken Hprint Hpending Herror HhistoryRoom Htag Ha Hb Hc Hstate Htop Hfalse
     Hready Hrename Hbudget Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput)
   as (final & index & fs & Hrun & Hstep & Hformula & Hderive & Hnext & Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop & Hsafe).
   exists final,(Protocol.OK (length (Protocol.history logical))),(AxiomReflProtocol.logical_after logical fs index).
   split;[exact Hrun|]. split;[exact Hstep|]. split;[exact Hnext|]. split;[|exact Hsafe].
   unfold NativeCommandBoundary.io. repeat first [assumption|split].
 - destruct (AxiomRejectionProtocol.generated_rejected s logical bs ns ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations
     Hencoding Hconcrete ltac:(lia) Htoken Hprint Hpending Herror Htag Ha Hb Hc
     (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
     (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) (NativeState.schema_representation _ _ Hstate)
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput)
   as (final & Hequal & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hlengths & Hclear & HnextTop & Hsafe).
   destruct (ReadFour.generated_reads s 11 ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations
     ltac:(lia) Htoken Hprint Hpending Herror ltac:(unfold maximum;lia) Hencoding Htag Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hinput)
   as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargprint & Hin & Hout).
   exists final,Protocol.NO,logical. split;[exact Hrun|]. split;[exact Hstep|]. split;[constructor;assumption|].
   split;[|exact Hsafe]. unfold NativeCommandBoundary.io. split.
   + rewrite Hequal. exact Hin.
   + split.
     * rewrite Hequal. change (stdout (ReadFour.fourth_state s ch chars tag sep1 a sep2 b sep3 c sep4 tail)++Protocol.reply_bytes Protocol.NO=stdout s++Protocol.reply_bytes Protocol.NO).
       exact (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout).
     * split;[rewrite Hlengths;exact Htoken|]. split;[rewrite Hlengths;exact Hprint|]. split;[exact Hclear|].
       rewrite Hequal,AxiomRejectionProtocol.result_meta_other by lia. apply ReadFour.fourth_meta_other;lia.
Qed.
End NativeAxiomTotal.
