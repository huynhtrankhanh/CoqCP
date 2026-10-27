From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeSchemaLift LogicalHistory SchemaRepresentation SchemaMetadata
 NameClassRefinement NameTheoremRefinement NameSchemaRefinement TokenByte Representation ClassStorage HistoryRefinement NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeNamedCommands.
Import IndexExecution SipHashExecution.
Module Class.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 58 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 9 [value] name) reply target /\
    NativeState.represents final target /\ (Guarantees.safe logical -> Guarantees.safe target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (NameClassRefinement.generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate)
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 9 57 [] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 9 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Class.
Module TheoremName.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name -> LogicalHistory.valid logical ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 48 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 20 [value] name) reply target /\
    NativeState.represents final target /\ (Guarantees.safe logical -> Guarantees.safe target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hvalid Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (NameTheoremRefinement.generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hvalid
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate)
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 20 50 [48] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 20 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End TheoremName.
Module Schema.
Theorem generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = 51 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> Protocol.valid_name name ->
  NativeState.represents s logical ->
  Z.of_nat (length (Protocol.bindings logical)) < maximum ->
  Z.of_nat (length (memory s arraydef_0__names) + length name) <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = 51 :: first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  exists final reply target, execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 23 [value] name) reply target /\
    NativeState.represents final target /\ (Guarantees.safe logical -> Guarantees.safe target).
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hword Hname Hstate HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput.
 destruct (NameSchemaRefinement.generated_total_protocol s logical bs ns value name first_separator middle_separator last_separator tail observations
   Hmeta Htoken Hbuffer Hpending Herror Hword Hname
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate)
   (NativeState.history_representation _ _ Hstate) (NativeState.name_representation _ _ Hstate) (SchemaRepresentation.metadata _ _ (NativeState.schema_representation _ _ Hstate))
   HbindingRoom HnameRoom Hfirst Hmiddle Hlast Hinput)
 as (final & reply & target & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hmetadata).
 exists final,reply,target. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - exact (NativeSchemaLift.canonical 23 50 [51] s bs ns first_separator
    (decimalBytes value++middle_separator::name++last_separator::tail) observations final _ logical (Protocol.Req 23 [value] name) reply target
    ltac:(lia) ltac:(lia) eq_refl eq_refl Hmeta Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory Hnames).
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Schema.
End NativeNamedCommands.
