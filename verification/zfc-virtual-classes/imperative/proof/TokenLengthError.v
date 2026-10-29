From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module TokenLengthError.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Theorem generated_full_byte (f:Frame) ch :
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)6=1024 ->
 (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 0<=ch<256 -> ~separator ch -> meta_value(machine f)17=0 ->
 execLocal(byte_body ch)f=Some(Stop,setMachine f(store_meta(machine f)8 1)).
Proof.
 intros Hmeta Hsize Htoken Hbyte Hnosep Hdone.
 rewrite(generated_byte_body f 1024%nat ch Hmeta Hsize ltac:(lia) Htoken Hbyte).
 unfold tick. rewrite(bool_decide_false _) by exact Hnosep. rewrite(bool_decide_true _) by reflexivity.
 unfold byte_outcome. rewrite meta_store_other by lia. rewrite Hdone,bool_decide_false by congruence.
 rewrite meta_store_same by lia. rewrite bool_decide_true by discriminate. reflexivity.
Qed.
Theorem overflowing_tape chars (f:Frame) size ch tail :
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)6=Z.of_nat size ->
 (size+length chars=1024)%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)17=0 -> meta_value(machine f)8=0 ->
 Forall(fun c=>0<=c<256 /\ ~separator c) chars -> 0<=ch<256 -> ~separator ch ->
 stdin(machine f)=chars++ch::tail ->
 tape_execution byte_body f (setMachine f (withInput(store_meta(put_many(machine f)size chars)8 1)tail)).
Proof.
 induction chars as [|c chars IH] in f,size|-*.
 - intros Hmeta Hsize Hlimit Htoken Hdone Herror Hchars Hbyte Hnosep Hinput.
   cbn [List.app length put_many] in Hinput|-*. assert(Hsize':size=1024%nat) by lia. subst size.
   apply(tape_stop byte_body f ch tail);[exact Hinput|lia|].
   rewrite(generated_full_byte (setMachine f(withInput(machine f)tail)) ch Hmeta Hsize Htoken Hbyte Hnosep Hdone). reflexivity.
 - intros Hmeta Hsize Hlimit Htoken Hdone Herror Hchars Hbyte Hnosep Hinput.
   inversion Hchars as [|c' rest Hhead Hrest];subst c' rest. destruct Hhead as [Hc Hnc].
   set(read:=setMachine f(withInput(machine f)(chars++ch::tail))).
   set(next:=setMachine read(put_byte(machine read)size c)).
   assert(Hbody:execLocal(byte_body c)read=Some(KeepGoing,next)).
   { apply generated_data_byte;try assumption;cbn [length] in Hlimit;lia. }
   assert(Hnext:tape_execution byte_body next (setMachine next(withInput(store_meta(put_many(machine next)(S size)chars)8 1)tail))).
   { apply IH.
     - change (17<length(memory(put_byte(machine read)size c)arraydef_0__meta))%nat. rewrite put_meta_length. exact Hmeta.
     - change(meta_value(put_byte(machine read)size c)6=Z.of_nat(S size)). apply put_byte_count. change(6<length(memory(machine f)arraydef_0__meta))%nat. lia.
     - cbn [length] in Hlimit. lia.
     - change(1024<=length(memory(put_byte(machine read)size c)arraydef_0__token))%nat. rewrite put_token_length. exact Htoken.
     - change(meta_value(put_byte(machine read)size c)17=0). rewrite put_byte_meta_other by lia. exact Hdone.
     - change(meta_value(put_byte(machine read)size c)8=0). rewrite put_byte_meta_other by lia. exact Herror.
     - exact Hrest.
     - exact Hbyte.
     - exact Hnosep.
     - reflexivity. }
   assert(Hrel:setMachine next(withInput(store_meta(put_many(machine next)(S size)chars)8 1)tail)=
    setMachine f(withInput(store_meta(put_many(machine f)size(c::chars))8 1)tail)).
   { unfold next,read. cbn [machine setMachine put_many]. rewrite put_byte_input,put_many_input. reflexivity. }
   rewrite <-Hrel. apply(tape_next byte_body f c (chars++ch::tail) next);try assumption. lia.
Qed.
End TokenLengthError.
