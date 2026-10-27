From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStateFrames NativeProtocolLift LogicalHistory
 ModusPonensRejection GeneralizeTotal RestateRefinement InspectRefinement
 TokenByte Representation ClassStorage HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeTheoremCommands.
Import IndexExecution SipHashExecution.
Module MP.
Theorem generated_total_protocol s logical bs ns i j first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> Z.of_nat i <= maximum -> Z.of_nat j <= maximum ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 50 :: first_separator :: decimalBytes i ++ middle_separator :: decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 12 [i;j] []) reply next /\
    NativeState.represents final next /\ LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Hstate Hsep1 Hsep2 Hsep3 Hin.
 destruct (ModusPonensRejection.generated_total_protocol s logical bs ns i j first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hsep3 Hin)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & HnextValid).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 12 49 [50] s bs ns first_separator
    (decimalBytes i++middle_separator::decimalBytes j++last_separator::tail) observations final _ logical (Protocol.Req 12 [i;j] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact HnextValid|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End MP.
Module Generalize.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat (length (Protocol.formulas logical)) <= 9223372036854775807 ->
  Z.of_nat (length (Protocol.history logical)) < maximum -> Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 13 [value] []) reply next /\
    NativeState.represents final next /\ LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (GeneralizeTotal.generated_total_protocol s logical bs ns value first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hbound Hhistorybound Hvalue Hvalid (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & HnextValid).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 13 49 [51] s bs ns first_separator
    (decimalBytes value++last_separator::tail) observations final _ logical (Protocol.Req 13 [value] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact HnextValid|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Generalize.
Module Restate.
Theorem generated_total_protocol s logical bs ns i j first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat i <= maximum -> Z.of_nat j <= maximum -> Z.of_nat (length (Protocol.history logical)) < maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 56 :: first_separator :: decimalBytes i ++ middle_separator :: decimalBytes j ++ last_separator :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 18 [i;j] []) reply next /\
    NativeState.represents final next /\ LogicalHistory.valid next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid Hstate Hsep1 Hsep2 Hsep3 Hin.
 destruct (RestateRefinement.generated_total_protocol s logical bs ns i j first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hiword Hjword Hbound Hvalid (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hsep3 Hin)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & HnextValid).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 18 49 [56] s bs ns first_separator
    (decimalBytes i++middle_separator::decimalBytes j++last_separator::tail) observations final _ logical (Protocol.Req 18 [i;j] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact HnextValid|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Restate.
Module Inspect.
Theorem generated_total_protocol s logical bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 50 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 57 :: first_separator :: decimalBytes value ++ last_separator :: tail ->
  exists final reply,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 19 [value] []) reply logical /\
    NativeState.represents final logical /\ LogicalHistory.valid logical /\ (Guarantees.safe logical -> Guarantees.safe logical).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid Hstate Hsep1 Hsep2 Hin.
 destruct (InspectRefinement.generated_total_protocol s logical bs ns value first_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hvalue Hvalid (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) Hsep1 Hsep2 Hin)
 as (final & reply & Hrun & Hstep & Harena & Hclasses & Hhistory).
 exists final,reply. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 19 49 [57] s bs ns first_separator
    (decimalBytes value++last_separator::tail) observations final _ logical (Protocol.Req 19 [value] []) reply logical
    ltac:(lia) ltac:(lia) _ eq_refl eq_refl Hmeta Htoken Hpending Herror Hsep1 Hin Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - split;[exact Hvalid|]. intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Inspect.
End NativeTheoremCommands.
