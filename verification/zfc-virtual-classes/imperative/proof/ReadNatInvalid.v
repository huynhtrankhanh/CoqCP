From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ReadNatInvalid.
Import IndexExecution SipHashExecution ReadNatExecution.
Definition invalid_frame (f:Frame) ch := setMachine (setNum f vardef_0__readNat_digit ch) (store_meta (machine f) 14 0).
Theorem generated_nondigit f total remaining index ch :
 total-Z.of_nat remaining-1=Z.of_nat index ->
 (index<length(memory(machine f) arraydef_0__token))%nat ->
 (14<length(memory(machine f) arraydef_0__meta))%nat ->
 List.nth index (memory(machine f) arraydef_0__token) 0=ch ->
 0<=ch<256 -> (ch<48 \/ 57<ch) ->
 execLocal (digit_body total remaining) f=Some(Stop,invalid_frame f ch).
Proof.
 intros Hindex Hcapacity Hmeta Hch Hbyte Hbad.
 assert(Hraw:coerceInt ch 64=ch) by(apply coerce_word;unfold word,maximum;lia).
 destruct f as [s bs ns]. cbn [machine nums] in *.
 destruct Hbad as [Hbad|Hbad].
 all:
 unfold digit_body.
 all: repeat first [rewrite execLocal_bind |rewrite ReadTokenExecution.exec_drop_assoc |rewrite exec_drop_lift |rewrite local_done |rewrite Hindex |progress cbn [bind optionBind fst snd]].
 all: rewrite (local_read_token {|machine:=s;bools:=bs;nums:=ns|}(Z.of_nat index)) by (now rewrite Nat2Z.id).
 all: repeat first [rewrite execLocal_bind |rewrite ReadTokenExecution.exec_drop_assoc |rewrite exec_drop_lift
  |rewrite local_done |rewrite local_read_meta by (cbn [machine setMachine];lia)
  |rewrite local_put_meta by (cbn [machine setMachine];lia)
  |rewrite local_get |rewrite local_set |rewrite Hindex |rewrite Nat2Z.id |rewrite Hch |rewrite Hraw
  |rewrite dropWithinLoop_4
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by lia|rewrite (bool_decide_false P) by lia] end
  |progress cbv beta iota zeta delta [bind subInt addInt multInt divIntUnsigned shortCircuitOr optionBind fst snd machine setMachine setNum nums bools Imperative.update]
  |match goal with |- context [decide ?P] => first [rewrite (decide_True (P:=P)) by congruence|rewrite (decide_False (P:=P)) by congruence] end].
 all: reflexivity.
Qed.
Theorem generated_nondigit_loop prefix bad suffix f total offset value :
 (offset+length prefix+S(length suffix)=total)%nat ->
 (total<=length(memory(machine f) arraydef_0__token))%nat ->
 (14<length(memory(machine f) arraydef_0__meta))%nat ->
 (forall i,(i<length prefix+S(length suffix))%nat ->
  List.nth(offset+i)(memory(machine f) arraydef_0__token)0=List.nth i(prefix++bad::suffix)0) ->
 nums f vardef_0__readNat_value=value -> 0<=value ->
 Forall(fun ch=>48<=ch<=57)prefix -> number_from value prefix<=maximum ->
 0<=bad<256 -> (bad<48 \/ 57<bad) ->
 execLocal(loop (length prefix+S(length suffix)) (digit_body(Z.of_nat total))) f=
 Some(tt,invalid_frame(run_digits f value prefix)bad).
Proof.
 induction prefix as [|ch prefix IH] in f,offset,value|-*.
 - intros Htotal Hcap Hmeta Hentry Hvalue Hnonneg Hdigits Hbound Hbyte Hbad.
   change (execLocal (loop (S(length suffix)) (digit_body(Z.of_nat total))) f = Some(tt,invalid_frame f bad)). rewrite loop_S,execLocal_bind.
   assert(Hchar:List.nth offset (memory(machine f) arraydef_0__token) 0=bad).
   { specialize(Hentry 0%nat ltac:(lia)). rewrite Nat.add_0_r in Hentry. exact Hentry. }
   rewrite (generated_nondigit f (Z.of_nat total) (length suffix) offset bad).
   2:{ cbn [length] in Htotal. replace total with (offset+S(length suffix))%nat by lia. rewrite Nat2Z.inj_add,Nat2Z.inj_succ. lia. }
   2:{ cbn [length] in Htotal. lia. }
   all:try assumption.
   reflexivity.
 - intros Htotal Hcap Hmeta Hentry Hvalue Hnonneg Hdigits Hbound Hbyte Hbad.
   inversion Hdigits as [|ch' prefix' Hch Hrest];subst ch' prefix'.
   assert(Hnext:0<=10*value+(ch-48)) by lia.
   assert(Hroom:10*value+(ch-48)<=maximum).
   { pose proof(number_from_ge (10*value+(ch-48)) prefix Hnext Hrest). cbn [number_from] in Hbound. lia. }
   assert(Hindex:Z.of_nat total-Z.of_nat(length prefix+S(length suffix))-1=Z.of_nat offset) by (cbn [length] in Htotal;lia).
   assert(Hchar:List.nth offset(memory(machine f) arraydef_0__token)0=ch).
   { specialize(Hentry 0%nat ltac:(cbn [length];lia)). now rewrite Nat.add_0_r in Hentry. }
   change (execLocal (loop (S(length prefix+S(length suffix))) (digit_body(Z.of_nat total))) f = Some(tt,invalid_frame(run_digits(digit_frame f ch (10*value+(ch-48))) (10*value+(ch-48)) prefix)bad)).
   rewrite loop_S,execLocal_bind.
   rewrite(generated_digit f (Z.of_nat total) (length prefix+S(length suffix)) offset ch value Hindex ltac:(cbn [length] in Htotal;lia) Hchar Hvalue Hch Hnonneg Hroom).
   cbn [optionBind fst snd run_digits]. apply(IH (digit_frame f ch (10*value+(ch-48))) (S offset) (10*value+(ch-48))).
   + cbn [length] in Htotal. lia.
   + exact Hcap.
   + exact Hmeta.
   + intros i Hi. change(List.nth(S offset+i)(memory(machine f) arraydef_0__token)0=List.nth i(prefix++bad::suffix)0).
     replace (S offset+i)%nat with (offset+S i)%nat by lia. apply(Hentry(S i)). cbn [length]. lia.
   + apply digit_value.
   + exact Hnext.
   + exact Hrest.
   + exact Hbound.
   + exact Hbyte.
   + exact Hbad.
Qed.
Theorem generated_readNat_nondigit s bs ns tokenstate prefix bad suffix :
 exec(funcdef_0__readToken (fun _=>false)(fun _=>0))s=Some(tt,tokenstate) ->
 (17<length(memory tokenstate arraydef_0__meta))%nat -> meta_value tokenstate 14<>0 ->
 meta_value tokenstate 6=Z.of_nat(length(prefix++bad::suffix)) ->
 (length(prefix++bad::suffix)<=length(memory tokenstate arraydef_0__token))%nat ->
 (forall i,(i<length(prefix++bad::suffix))%nat ->
   List.nth i(memory tokenstate arraydef_0__token)0=List.nth i(prefix++bad::suffix)0) ->
 Forall(fun ch=>48<=ch<=57)prefix -> number_from 0 prefix<=maximum ->
 0<=bad<256 -> (bad<48 \/ 57<bad) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,store_meta(store_meta tokenstate 14 0)11(number_from 0 prefix)).
Proof.
 intros Hreader Hmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbyte Hbad.
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:Frame).
 set(start:=setNum(setMachine f tokenstate) vardef_0__readNat_value 0).
 set(after:=invalid_frame(run_digits start 0 prefix)bad).
 assert(Hrun:execLocal(digit_loop(meta_value tokenstate 6))start=Some(tt,after)).
 { rewrite Hcount,actual_digit_loop,Nat2Z.id. unfold after.
   replace(length(prefix++bad::suffix)) with (length prefix+S(length suffix))%nat by (rewrite length_app;reflexivity).
   apply(generated_nondigit_loop prefix bad suffix start (length prefix+S(length suffix)) 0 0).
   - reflexivity.
   - rewrite length_app in Hcapacity. exact Hcapacity.
   - change (14<length(memory tokenstate arraydef_0__meta))%nat. lia.
   - intros i Hi. rewrite Nat.add_0_l. apply Hentries. rewrite length_app. exact Hi.
   - reflexivity.
   - lia.
   - exact Hdigits.
   - exact Hbound.
   - exact Hbyte.
   - exact Hbad. }
 assert(Hmachine:machine after=store_meta tokenstate 14 0).
 { unfold after,invalid_frame. cbn [machine setMachine setNum]. rewrite run_machine. reflexivity. }
 assert(Hvalue:nums after vardef_0__readNat_value=number_from 0 prefix).
 { unfold after,invalid_frame. cbn [nums setMachine setNum].
   apply run_value. reflexivity. }
 unfold funcdef_0__readNat. rewrite exec_eliminate,actual_body. fold f.
 rewrite(read_composition funcdef_0__readToken digit_loop f tokenstate after Hreader ltac:(lia) Hvalid Hrun ltac:(rewrite Hmachine,store_meta_length;lia)).
 cbn [optionBind fst snd machine setMachine]. rewrite Hvalue,Hmachine. reflexivity.
Qed.
Theorem generated_bad_token s bs ns prefix bad suffix sep tail :
 (17<length(memory s arraydef_0__meta))%nat ->
 (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 ->
 (length(prefix++bad::suffix)<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)(prefix++bad::suffix) ->
 TokenByteExecution.separator sep -> stdin s=(prefix++bad::suffix)++sep::tail ->
 Forall(fun ch=>48<=ch<=57)prefix -> number_from 0 prefix<=maximum ->
 (bad<48 \/ 57<bad) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,store_meta(store_meta(ReadTokenExecution.read_result s (prefix++bad::suffix) tail)14 0)11(number_from 0 prefix)).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hsep Hinput Hdigits Hbound Hbad.
 assert(Hpositive:(0<length(prefix++bad::suffix))%nat) by (rewrite length_app;cbn [length];lia).
 assert(Hbadbyte:0<=bad<256).
 { apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. apply in_or_app. right. now left. }
 apply (generated_readNat_nondigit s bs ns _ prefix bad suffix).
 - apply(ReadTokenExecution.generated_readToken_none s (fun _=>false)(fun _=>0) (prefix++bad::suffix) sep tail);try assumption;lia.
 - now rewrite ReadTokenExecution.result_meta_length.
 - rewrite ReadTokenExecution.result_valid by exact Hmeta. discriminate.
 - now apply ReadTokenExecution.result_count.
 - unfold ReadTokenExecution.read_result. rewrite store_meta_other by discriminate.
   change(length(prefix++bad::suffix)<=length(memory(store_meta(ReadTokenExecution.put_many(ReadTokenExecution.reset s)0(prefix++bad::suffix))17 (1%Z))arraydef_0__token))%nat.
   rewrite store_meta_other by discriminate. rewrite ReadTokenExecution.put_many_token_length,ReadTokenExecution.reset_token. lia.
 - intros i Hi. apply(ReadTokenExecution.result_token_entry s (prefix++bad::suffix) tail i);[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
 - exact Hdigits.
 - exact Hbound.
 - exact Hbadbyte.
 - exact Hbad.
Qed.
End ReadNatInvalid.
