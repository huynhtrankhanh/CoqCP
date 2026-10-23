From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadOne ReadTwo ReadFour DecimalInput
  CommandArgs ArenaFrame AxiomCommand.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ReadFive.
Import IndexExecution SipHashExecution.
Definition fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail :=
  ReadFour.fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 (decimalBytes e++sep5::tail).
Definition fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail :=
  DecimalInput.encoded_result (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) e tail.
Lemma fifth_meta_length s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail :
  length (memory (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold fifth_state,fourth_state. now rewrite DecimalInput.encoded_meta_length,ReadFour.fourth_meta_length. Qed.
Lemma fifth_other s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail name :
  name<>arraydef_0__meta -> name<>arraydef_0__token ->
  memory (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) name=memory s name.
Proof.
  intros Hm Ht. unfold fifth_state,fourth_state. rewrite DecimalInput.encoded_other by assumption.
  now apply ReadFour.fourth_other.
Qed.
Lemma fifth_meta_other s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail i :
  (17<length (memory s arraydef_0__meta))%nat ->
  i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat -> i<>17%nat ->
  meta_value (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) i=meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold fifth_state,fourth_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite ReadFour.fourth_meta_length;assumption).
  now apply ReadFour.fourth_meta_other.
Qed.
Lemma fifth_storage s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail :
  (17<length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail).
Proof.
  intro Hmeta. eapply ArenaFrame.storage_trans;[apply ReadFour.fourth_storage;exact Hmeta|].
  apply CommandArgs.encoded_storage. unfold fourth_state. now rewrite ReadFour.fourth_meta_length.
Qed.
Lemma fourth_clear s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail :
  (17<length (memory s arraydef_0__meta))%nat ->
  meta_value (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) 15=0.
Proof.
  intro Hmeta. unfold fourth_state,ReadFour.fourth_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite ReadFour.third_meta_length;try exact Hmeta;lia).
  unfold ReadFour.third_state. rewrite DecimalInput.encoded_meta_other by (try rewrite ReadFour.second_meta_length;try exact Hmeta;lia).
  unfold ReadFour.second_state,ReadTwo.second_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite ReadTwo.first_meta_length;try exact Hmeta;lia).
  unfold ReadTwo.first_state,ReadOne.argument_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length;try exact Hmeta;lia).
  now apply CommandArgs.pending_cleared.
Qed.
Theorem generated_reads s opcode ch chars a b c d e sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  (17<length (memory s arraydef_0__meta))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum -> Z.of_nat e<=maximum ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
  stdin s=chars++sep0::decimalBytes a++sep1::decimalBytes b++sep2::decimalBytes c++sep3::decimalBytes d++sep4::decimalBytes e++sep5::tail ->
  let suffix:=decimalBytes e++sep5::tail in
  let op:=ReadFour.opcode_state s ch chars a sep1 b sep2 c sep3 d sep4 suffix in
  let first:=ReadFour.first_state s ch chars a sep1 b sep2 c sep3 d sep4 suffix in
  let second:=ReadFour.second_state s ch chars a sep1 b sep2 c sep3 d sep4 suffix in
  let third:=ReadFour.third_state s ch chars a sep1 b sep2 c sep3 d sep4 suffix in
  let fourth:=fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail in
  let fifth:=fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail in
  AxiomCommand.read_result funcdef_0__readNat s op (Z.of_nat opcode) observations /\
  AxiomCommand.read_result funcdef_0__readNat op first (Z.of_nat a) observations /\
  AxiomCommand.read_result funcdef_0__readNat first second (Z.of_nat b) observations /\
  AxiomCommand.read_result funcdef_0__readNat second third (Z.of_nat c) observations /\
  AxiomCommand.read_result funcdef_0__readNat third fourth (Z.of_nat d) observations /\
  AxiomCommand.read_result funcdef_0__readNat fourth fifth (Z.of_nat e) observations /\
  (20<=length (memory fifth arraydef_0__printBuffer))%nat /\ stdin fifth=tail /\ stdout fifth=stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding Ha Hb Hc Hd He Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  destruct (ReadFour.generated_reads s opcode ch chars a b c d sep0 sep1 sep2 sep3 sep4
    (decimalBytes e++sep5::tail) observations Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding
    Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin)
    as (Hop & Hfirst & Hsecond & Hthird & Hfourth & Hfourthbuffer & Hinput & Houtput).
  set (fourth:=fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail).
  pose proof Hfourth as [_ [Hfourthmeta [_ [_ Hfourtherror]]]].
  assert (Hfourthtoken:(1024<=length (memory fourth arraydef_0__token))%nat).
  { unfold fourth,fourth_state,ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state,
      ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length. }
  destruct (ReadFour.encoded_read fourth e sep5 tail observations Hfourthmeta Hfourthtoken
    (fourth_clear s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail Hmeta) Hfourtherror He Hsep5 Hinput)
    as (Hfifth & Hfifthtoken & Hfifthclear & Hfifthinput & Hfifthoutput).
  change (stdout fourth=stdout s) in Houtput.
  assert (Hout:stdout (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail)=stdout s).
  { unfold fifth_state. change (stdout (DecimalInput.encoded_result fourth e tail)=stdout s). now rewrite Hfifthoutput. }
  assert (Hprint:(20<=length (memory (fifth_state s ch chars a sep1 b sep2 c sep3 d sep4 e sep5 tail) arraydef_0__printBuffer))%nat).
  { rewrite fifth_other by discriminate. exact Hbuffer. }
  split;[exact Hop|]. split;[exact Hfirst|]. split;[exact Hsecond|].
  split;[exact Hthird|]. split;[exact Hfourth|]. split;[exact Hfifth|]. repeat split;assumption.
Qed.
End ReadFive.
