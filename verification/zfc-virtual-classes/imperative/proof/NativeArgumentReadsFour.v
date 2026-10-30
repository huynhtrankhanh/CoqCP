From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadNat ReadNatLeading ReadOne ReadTwo ReadFour DecimalInput CommandInput CommandArgs AxiomCommand NativeArgumentWhitespace NativeArgumentReadsTwo NativeArgumentReadsTwoFull.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeArgumentReadsFour.
Import IndexExecution SipHashExecution.
Lemma second_suffix s ch chars a sep1 b sep2 tail1 tail2 :
 ReadTwo.second_state s ch chars a sep1 b sep2 tail1 = withInput(ReadTwo.second_state s ch chars a sep1 b sep2 tail2)tail1.
Proof.
 unfold ReadTwo.second_state,ReadTwo.first_state.
 rewrite(NativeArgumentReadsTwo.argument_suffix s ch chars a sep1 (decimalBytes b++sep2::tail1) (decimalBytes b++sep2::tail2)).
 rewrite NativeArgumentWhitespace.encoded_result_input. apply NativeArgumentReadsTwo.encoded_suffix.
Qed.
Lemma read_leading s value prefix sep tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> Z.of_nat value<=maximum -> TokenByteExecution.separator sep ->
 Forall TokenByteExecution.separator prefix -> stdin s=prefix++decimalBytes value++sep::tail ->
 let t:=DecimalInput.encoded_result s value tail in
 AxiomCommand.read_result funcdef_0__readNat s t (Z.of_nat value) observations /\
 (1024<=length(memory t arraydef_0__token))%nat /\ meta_value t 15=0 /\ stdin t=tail /\ stdout t=stdout s.
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix Hin t.
 pose proof(ReadNatLeading.generated_encoded s (fun _=>false)(fun _=>0) value prefix sep tail
  Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix Hin) as Hplain.
 pose proof(ReadNatExecution.generated_readNat_observed _ _ _ _ observations Hplain) as Hrun.
 destruct(DecimalInput.encoded_result_correct s value tail Hmeta Hvalue) as [Hnumber [Hinput Houtput]].
 assert(Htmeta:(17<length(memory t arraydef_0__meta))%nat) by (unfold t;rewrite DecimalInput.encoded_meta_length;exact Hmeta).
 assert(Htvalid:meta_value t 14=1) by (unfold t;apply CommandArgs.encoded_valid;exact Hmeta).
 assert(Hterror:meta_value t 8=0) by (unfold t;rewrite DecimalInput.encoded_meta_other by lia;exact Herror).
 assert(Httoken:(1024<=length(memory t arraydef_0__token))%nat) by (unfold t;rewrite DecimalInput.encoded_token_length;exact Htoken).
 assert(Htclear:meta_value t 15=0) by (unfold t;rewrite DecimalInput.encoded_meta_other by lia;exact Hpending).
 unfold AxiomCommand.read_result. repeat split;assumption.
Qed.
Theorem generated_reads s opcode ch chars a b c d sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 (20<=length(memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
 Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 ->
 Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
 stdin s=chars++sep0::sp1++decimalBytes a++sep1::sp2++decimalBytes b++sep2::sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail ->
 let op:=CommandInput.parsed s ch chars (sp1++decimalBytes a++sep1::sp2++decimalBytes b++sep2::sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail) in
 let first:=ReadOne.argument_state s ch chars a sep1 (sp2++decimalBytes b++sep2::sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail) in
 let second:=ReadTwo.second_state s ch chars a sep1 b sep2 (sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail) in
 let third:=DecimalInput.encoded_result second c (sp4++decimalBytes d++sep4::tail) in
 let fourth:=ReadFour.fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail in
 AxiomCommand.read_result funcdef_0__readNat s op (Z.of_nat opcode) observations /\
 AxiomCommand.read_result funcdef_0__readNat op first (Z.of_nat a) observations /\
 AxiomCommand.read_result funcdef_0__readNat first second (Z.of_nat b) observations /\
 AxiomCommand.read_result funcdef_0__readNat second third (Z.of_nat c) observations /\
 AxiomCommand.read_result funcdef_0__readNat third fourth (Z.of_nat d) observations /\
 (20<=length(memory fourth arraydef_0__printBuffer))%nat /\ stdin fourth=tail /\ stdout fourth=stdout s.
Proof.
 intros Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hin. cbn zeta.
 pose proof(NativeArgumentReadsTwoFull.generated_reads s (fun _=>false)(fun _=>0) opcode ch chars a b sep0 sp1 sep1 sp2 sep2
   (sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail) observations Hmeta Htoken Hbuffer Hpending Herror Hopcode Hencoding
   Ha Hb Hsep0 Hsep1 Hsep2 Hsp1 Hsp2 Hin) as Hreads.
 destruct Hreads as [Hop [Hfirst [Hsecond [Hopmeta [Hopnumber [Hopvalid [Hoperror
   [Hfirstmeta [Hfirstnumber [Hfirstvalid [Hfirsterror [Hsecondmeta [Hsecondbuffer
   [Hsecondnumber [Hsecondvalid [Hseconderror [Hsecondinput Hsecondoutput]]]]]]]]]]]]]]]]].
 set(second:=ReadTwo.second_state s ch chars a sep1 b sep2 (sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail)).
 assert(Hsecondtoken:(1024<=length(memory second arraydef_0__token))%nat).
 { unfold second,ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
   rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length. exact Htoken. }
 assert(Hsecondclear:meta_value second 15=0).
 { unfold second,ReadTwo.second_state.
   rewrite DecimalInput.encoded_meta_other by (try rewrite ReadTwo.first_meta_length;try exact Hmeta;lia).
   unfold ReadTwo.first_state,ReadOne.argument_state.
   rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length;try exact Hmeta;lia).
   apply CommandArgs.pending_cleared;lia. }
 destruct(read_leading second c sp3 sep3 (sp4++decimalBytes d++sep4::tail) observations
   Hsecondmeta Hsecondtoken Hsecondclear Hseconderror Hc Hsep3 Hsp3 Hsecondinput)
   as [Hthird [Hthirdtoken [Hthirdclear [Hthirdinput Hthirdoutput]]]].
 destruct Hthird as [Hthirdrun [Hthirdmeta [Hthirdnumber [Hthirdvalid Hthirderror]]]].
 set(third:=DecimalInput.encoded_result second c (sp4++decimalBytes d++sep4::tail)).
 destruct(read_leading third d sp4 sep4 tail observations Hthirdmeta Hthirdtoken Hthirdclear Hthirderror Hd Hsep4 Hsp4 Hthirdinput)
   as [Hfourth [Hfourthtoken [Hfourthclear [Hfourthinput Hfourthoutput]]]].
 assert(Hcanonical:DecimalInput.encoded_result third d tail=ReadFour.fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail).
 { unfold third,second,ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state.
   rewrite(second_suffix s ch chars a sep1 b sep2 (sp3++decimalBytes c++sep3::sp4++decimalBytes d++sep4::tail)
    (decimalBytes c++sep3::decimalBytes d++sep4::tail)).
   rewrite NativeArgumentWhitespace.encoded_result_input.
   rewrite(NativeArgumentReadsTwo.encoded_suffix _ c (sp4++decimalBytes d++sep4::tail) (decimalBytes d++sep4::tail)).
   apply NativeArgumentWhitespace.encoded_result_input. }
 rewrite Hcanonical in Hfourth,Hfourthinput,Hfourthoutput.
 assert(Hfourthbuffer:(20<=length(memory (ReadFour.fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail)arraydef_0__printBuffer))%nat).
 { rewrite ReadFour.fourth_other by discriminate. exact Hbuffer. }
 assert(Houtput:stdout (ReadFour.fourth_state s ch chars a sep1 b sep2 c sep3 d sep4 tail)=stdout s).
 { rewrite Hfourthoutput. unfold third. rewrite Hthirdoutput. exact Hsecondoutput. }
 destruct Hfourth as [Hfourthrun [Hfourthmeta [Hfourthnumber [Hfourthvalid Hfourtherror]]]].
 unfold AxiomCommand.read_result. repeat split;assumption.
Qed.
End NativeArgumentReadsFour.
