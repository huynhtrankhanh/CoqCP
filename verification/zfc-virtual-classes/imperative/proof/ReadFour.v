From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadOne ReadTwo DecimalInput CommandInput CommandArgs ArenaFrame AxiomCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ReadFour.
Import IndexExecution SipHashExecution.
Definition opcode_state s ch chars a sep1 b sep2 c sep3 d sep4 tail :=
  ReadTwo.opcode_state s ch chars a sep1 b sep2 (decimalBytes c ++ sep3 :: decimalBytes d ++ sep4 :: tail).
Definition first_state s ch chars a sep1 b sep2 c sep3 d sep4 tail :=
  ReadTwo.first_state s ch chars a sep1 b sep2 (decimalBytes c ++ sep3 :: decimalBytes d ++ sep4 :: tail).
Definition second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail :=
  ReadTwo.second_state s ch chars a sep1 b sep2 (decimalBytes c ++ sep3 :: decimalBytes d ++ sep4 :: tail).
Definition third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail :=
  DecimalInput.encoded_result (second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) c (decimalBytes d ++ sep4 :: tail).
Definition fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail :=
  DecimalInput.encoded_result (third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) d tail.
Lemma second_meta_length s ch chars a sep1 b sep2 c sep3 d sep4 tail :
  length (memory (second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. apply ReadTwo.second_meta_length. Qed.
Lemma third_meta_length s ch chars a sep1 b sep2 c sep3 d sep4 tail :
  length (memory (third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold third_state. now rewrite DecimalInput.encoded_meta_length, second_meta_length. Qed.
Lemma fourth_meta_length s ch chars a sep1 b sep2 c sep3 d sep4 tail :
  length (memory (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold fourth_state. now rewrite DecimalInput.encoded_meta_length, third_meta_length. Qed.
Lemma fourth_other s ch chars a sep1 b sep2 c sep3 d sep4 tail name : name<>arraydef_0__meta -> name<>arraydef_0__token ->
  memory (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) name=memory s name.
Proof.
  intros Hm Ht. unfold fourth_state,third_state,second_state.
  rewrite !DecimalInput.encoded_other by assumption. now apply ReadTwo.second_other.
Qed.
Lemma fourth_meta_other s ch chars a sep1 b sep2 c sep3 d sep4 tail i :
  (17<length (memory s arraydef_0__meta))%nat ->
  i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat -> i<>17%nat ->
  meta_value (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) i=meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold fourth_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite third_meta_length; assumption).
  unfold third_state. rewrite DecimalInput.encoded_meta_other by (try rewrite second_meta_length; assumption).
  unfold second_state. now apply ReadTwo.second_meta_other.
Qed.
Lemma fourth_storage s ch chars a sep1 b sep2 c sep3 d sep4 tail :
  (17<length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail).
Proof.
  intro Hmeta. eapply ArenaFrame.storage_trans with
    (t:=second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail).
  - apply ReadTwo.second_storage. exact Hmeta.
  - eapply ArenaFrame.storage_trans with
      (t:=third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail).
    + apply CommandArgs.encoded_storage. now rewrite second_meta_length.
    + apply CommandArgs.encoded_storage. now rewrite third_meta_length.
Qed.
Lemma encoded_read s value sep tail observations :
  (17<length (memory s arraydef_0__meta))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat ->
  meta_value s 15=0 -> meta_value s 8=0 ->
  Z.of_nat value<=maximum -> TokenByteExecution.separator sep ->
  stdin s=decimalBytes value++sep::tail ->
  let t:=DecimalInput.encoded_result s value tail in
  AxiomCommand.read_result funcdef_0__readNat s t (Z.of_nat value) observations /\
  (1024<=length (memory t arraydef_0__token))%nat /\
  meta_value t 15=0 /\ stdin t=tail /\ stdout t=stdout s.
Proof.
  intros Hmeta Htoken Hpending Herror Hvalue Hsep Hin t.
  pose proof (DecimalInput.generated_readNat_encoded_observed s (fun _=>false) (fun _=>0) value sep tail observations
    Hmeta Htoken Hpending Herror Hvalue Hsep Hin) as Hrun.
  destruct (DecimalInput.encoded_result_correct s value tail Hmeta Hvalue) as [Hnumber [Hinput Houtput]].
  assert (Htmeta:(17<length (memory t arraydef_0__meta))%nat) by (unfold t;now rewrite DecimalInput.encoded_meta_length).
  assert (Htvalid:meta_value t 14=1) by (unfold t;now apply CommandArgs.encoded_valid).
  assert (Hterror:meta_value t 8=0).
  { unfold t. rewrite DecimalInput.encoded_meta_other by (try exact Hmeta;lia). exact Herror. }
  assert (Httoken:(1024<=length (memory t arraydef_0__token))%nat) by (unfold t;now rewrite DecimalInput.encoded_token_length).
  assert (Htclear:meta_value t 15=0).
  { unfold t. rewrite DecimalInput.encoded_meta_other by (try exact Hmeta;lia). exact Hpending. }
  unfold AxiomCommand.read_result. repeat split;assumption.
Qed.
Theorem generated_reads s opcode ch chars a b c d sep0 sep1 sep2 sep3 sep4 tail observations :
  (17<length (memory s arraydef_0__meta))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  stdin s=chars++sep0::decimalBytes a++sep1::decimalBytes b++sep2::decimalBytes c++sep3::decimalBytes d++sep4::tail ->
  let op:=opcode_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
  let first:=first_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
  let second:=second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
  let third:=third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
  let fourth:=fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
  AxiomCommand.read_result funcdef_0__readNat s op (Z.of_nat opcode) observations /\
  AxiomCommand.read_result funcdef_0__readNat op first (Z.of_nat a) observations /\
  AxiomCommand.read_result funcdef_0__readNat first second (Z.of_nat b) observations /\
  AxiomCommand.read_result funcdef_0__readNat second third (Z.of_nat c) observations /\
  AxiomCommand.read_result funcdef_0__readNat third fourth (Z.of_nat d) observations /\
  (20<=length (memory fourth arraydef_0__printBuffer))%nat /\ stdin fourth=tail /\ stdout fourth=stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  pose proof (ReadTwo.generated_reads s (fun _=>false) (fun _=>0) opcode ch chars a b sep0 sep1 sep2
    (decimalBytes c++sep3::decimalBytes d++sep4::tail) observations Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding
    Ha Hb Hsep0 Hsep1 Hsep2 Hin) as Hreads.
  destruct Hreads as [Hop [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror
    [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer
    [Hsecondnumber [Hsecondvalid [Hseconderror [Hsecondinput Hsecondoutput]]]]]]]]]]]]]]]]].
  set (second:=second_state s ch chars a sep1 b sep2 c sep3 d sep4 tail).
  assert (Hsecondtoken:(1024<=length (memory second arraydef_0__token))%nat).
  { unfold second,second_state,ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length. }
  assert (Hsecondclear:meta_value second 15=0).
  { unfold second,second_state,ReadTwo.second_state.
    rewrite DecimalInput.encoded_meta_other by (try rewrite ReadTwo.first_meta_length;try exact Hmeta;lia).
    unfold ReadTwo.first_state,ReadOne.argument_state.
    rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length;try exact Hmeta;lia).
    now apply CommandArgs.pending_cleared. }
  destruct (encoded_read second c sep3 (decimalBytes d++sep4::tail) observations
    Hsecondmeta Hsecondtoken Hsecondclear Hseconderror Hc Hsep3 Hsecondinput)
    as [Hthird [Hthirdtoken [Hthirdclear [Hthirdinput Hthirdoutput]]]].
  destruct Hthird as [Hthirdrun [Hthirdmeta [Hthirdnumber [Hthirdvalid Hthirderror]]]].
  destruct (encoded_read (third_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) d sep4 tail observations
    Hthirdmeta Hthirdtoken Hthirdclear Hthirderror Hd Hsep4 Hthirdinput)
    as [Hfourth [Hfourthtoken [Hfourthclear [Hfourthinput Hfourthoutput]]]].
  assert (Hfourthbuffer:(20<=length (memory (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail) arraydef_0__printBuffer))%nat).
  { rewrite fourth_other by discriminate. exact Hbuffer. }
  assert (Houtput:stdout (fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail)=stdout s).
  { unfold fourth_state. rewrite Hfourthoutput. change (stdout (DecimalInput.encoded_result second c (decimalBytes d++sep4::tail))=stdout s). rewrite Hthirdoutput. exact Hsecondoutput. }
  destruct Hfourth as [Hfourthrun [Hfourthmeta [Hfourthnumber [Hfourthvalid Hfourtherror]]]].
  unfold AxiomCommand.read_result. repeat split;assumption.
Qed.
End ReadFour.
