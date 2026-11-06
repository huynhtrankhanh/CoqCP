From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativeByteTokenInfo NativeByteNumber ArenaFrame
 NativeState ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeNoncanonicalReaderState.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Definition result s chars tail := token_number (read_result s chars tail) chars.
Lemma meta_other s chars tail i : (17<length(memory s arraydef_0__meta))%nat ->
 i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>17%nat -> meta_value(result s chars tail)i=meta_value s i.
Proof. intros Hmeta H6 H11 H14 H17. unfold result,token_number. rewrite meta_store_other by exact H11. now apply result_meta_other. Qed.
Lemma array_other s chars tail name : name<>arraydef_0__meta -> name<>arraydef_0__token ->
 memory(result s chars tail)name=memory s name.
Proof. intros Hmeta Htoken. unfold result,token_number. rewrite store_meta_other by exact Hmeta. now apply result_other. Qed.
Lemma meta_length s chars tail : length(memory(result s chars tail)arraydef_0__meta)=length(memory s arraydef_0__meta).
Proof. unfold result,token_number. now rewrite store_meta_length,result_meta_length. Qed.
Lemma storage s chars tail : (17<length(memory s arraydef_0__meta))%nat -> ArenaFrame.storage s (result s chars tail).
Proof.
 intro Hmeta. split;[apply meta_length|]. split;[intros;now apply array_other|].
 repeat split;apply meta_other;try exact Hmeta;lia.
Qed.
Theorem represents s chars tail logical : (17<length(memory s arraydef_0__meta))%nat -> NativeState.represents s logical ->
 NativeState.represents (result s chars tail) logical.
Proof.
 intros Hmeta [Harena Hclasses Hhistory Hnames Hschemas]. constructor.
 - exact (ArenaFrame.storage_arena _ _ _ (storage s chars tail Hmeta) Harena).
 - unfold ClassStorage.represents in *. rewrite meta_other by (try exact Hmeta;lia). rewrite array_other by discriminate. exact Hclasses.
 - unfold HistoryRefinement.represents in *. rewrite meta_other by (try exact Hmeta;lia). rewrite array_other by discriminate. exact Hhistory.
 - unfold NameRepresentation.represents in *. rewrite !meta_other by (try exact Hmeta;lia). rewrite !array_other by discriminate. exact Hnames.
 - eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
   + apply meta_other;try exact Hmeta;lia.
   + apply array_other;discriminate.
Qed.
Theorem generated s bs ns logical chars spaces sep tail value observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator sep ->
 stdin s=spaces++chars++sep::tail -> ByteProtocol.decode_number chars=ByteProtocol.number value -> NativeState.represents s logical ->
 execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(result s chars tail,observations)) /\
 NativeState.represents(result s chars tail)logical /\ meta_value(result s chars tail)14=1 /\
 meta_value(result s chars tail)11=value /\ meta_value(result s chars tail)8=0 /\
 stdin(result s chars tail)=tail /\ stdout(result s chars tail)=stdout s /\
 (17<length(memory(result s chars tail)arraydef_0__meta))%nat.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput Hdecode Hstate.
 destruct(NativeByteTokenInfo.generated s chars spaces sep tail false Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 cbn [NativeByteTokenInfo.state] in *.
 pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
 destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
 pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
 assert(Hnumber:value=number_from 0 chars) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
 assert(Hrun:exec(funcdef_0__readNat bs ns)s=Some(tt,result s chars tail)).
 { unfold result. apply(ReadNatExecution.generated_readNat_from_token s bs ns (read_result s chars tail) chars);try assumption.
   rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia. }
 split;[now apply ReadNatExecution.generated_readNat_observed|]. split;[now apply represents|].
 unfold result,token_number. repeat rewrite meta_store_other by lia.
 split;[now apply result_valid|]. split;[rewrite Hnumber;apply meta_store_same;lia|].
 split;[exact Hclear|]. split;[exact Htail|]. split;[apply result_output|]. now rewrite store_meta_length,result_meta_length.
Qed.
End NativeNoncanonicalReaderState.
