From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeStateFrames NativeProtocolLift
 ClassEqualProtocol ClassMemberProtocol RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds
 TokenByte FormulaTopology ClassLookup Representation ClassStorage HistoryRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeClassBinaryCommands.
Import IndexExecution SipHashExecution.
Module Equal.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 7%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassEqual.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassEqual.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical -> ClassLookup.wellformed s ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 7 [a;b] []) reply next /\
    NativeState.represents final next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb Hstate Hgood Hfirst Hmiddle Hlast Hinput.
 destruct (ClassEqualProtocol.generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations
   Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate) Hgood
   (NativeState.history_representation _ _ Hstate) Hfirst Hmiddle Hlast Hinput)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 7 ch chars s bs ns first_separator
    (decimalBytes a++middle::decimalBytes b++last::tail) observations final _ logical (Protocol.Req 7 [a;b] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Equal.
Module Member.
Theorem generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations :
  decimalBytes 8%nat = ch :: chars ->
  (31 < length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  FormulaTopology.ordered s (length (Protocol.formulas logical)) -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  nth_error (Protocol.formulas logical) 0 = Some SetTheory.falsity ->
  (forall cls_a cls_b, Protocol.class_at logical a = Some cls_a -> Protocol.class_at logical b = Some cls_b ->
    RenameMemoClassMember.ready s (Protocol.formulas logical) a b cls_a cls_b /\
    Z.of_nat (length (Protocol.formulas logical) + RenameMemoClassMember.work s a b cls_a cls_b) <= RenameMemoResourceBounds.doubling_limit) ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  NativeState.represents s logical -> ClassLookup.wellformed s ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  exists final reply next,
    execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes reply; unreadInput := tail|}])) /\
    Protocol.step logical (Protocol.Req 8 [a;b] []) reply next /\
    NativeState.represents final next /\ (Guarantees.safe logical -> Guarantees.safe next).
Proof.
 intros Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb Hstate Hgood Hfirst Hmiddle Hlast Hinput.
 destruct (ClassMemberProtocol.generated_total_protocol ch chars s logical bs ns a b first_separator middle last tail observations
   Hencoding Hmeta Hsip Htop Htoken Hprint Hpending Herror Hfalse Hdomain Ha Hb
   (NativeState.formula_representation _ _ Hstate) (NativeState.class_representation _ _ Hstate) Hgood
   (NativeState.history_representation _ _ Hstate) Hfirst Hmiddle Hlast Hinput)
 as (final & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory).
 exists final,reply,next. split;[exact Hrun|]. split;[exact Hstep|]. split.
 - refine (NativeProtocolLift.canonical 8 ch chars s bs ns first_separator
    (decimalBytes a++middle::decimalBytes b++last::tail) observations final _ logical (Protocol.Req 8 [a;b] []) reply next
    ltac:(lia) ltac:(lia) _ eq_refl Hencoding ltac:(lia) Htoken Hpending Herror Hfirst Hinput Hrun Hstate Hstep Harena Hclasses Hhistory).
   unfold NativeStateFrames.nonbinding;repeat split;lia.
 - intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End Member.
End NativeClassBinaryCommands.
