From CoqCP Require Import Options.
From Trusted Require Import ByteProtocol.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ByteLexErrors.
Import ByteProtocol.
Lemma started_not_missing reversed input : reversed<>[] -> scan_token reversed input<>end_of_input.
Proof.
 induction input as [|byte input IH] in reversed|-*;intro Hnonempty.
 - cbn [scan_token]. destruct reversed;[contradiction|discriminate].
 - cbn [scan_token]. destruct(separator byte).
   + destruct reversed;[contradiction|discriminate].
   + destruct(Nat.eqb(length reversed)1024);[discriminate|]. apply IH. discriminate.
Qed.
Theorem missing input : read_token input=end_of_input -> Forall(fun ch=>separator ch=true)input.
Proof.
 unfold read_token. induction input as [|byte input IH];intro Hrun;[constructor|].
 cbn [scan_token] in Hrun. destruct(separator byte) eqn:Hsep.
 - constructor;[exact Hsep|now apply IH].
 - exfalso. exact(started_not_missing [byte] input ltac:(discriminate) Hrun).
Qed.
Lemma started_long reversed input tail : reversed<>[] -> scan_token reversed input=token_too_long tail ->
 exists payload bad, input=payload++bad::tail /\ Forall(fun ch=>separator ch=false)payload /\
 separator bad=false /\ (length reversed+length payload=1024)%nat.
Proof.
 induction input as [|byte input IH] in reversed|-*;intros Hnonempty Hrun.
 - cbn [scan_token] in Hrun. destruct reversed;discriminate.
 - cbn [scan_token] in Hrun. destruct(separator byte) eqn:Hsep.
   + destruct reversed;[contradiction|discriminate].
   + destruct(Nat.eqb(length reversed)1024) eqn:Hlimit.
     * apply Nat.eqb_eq in Hlimit. inversion Hrun;subst. exists [],byte. cbn. split;[reflexivity|]. split;[constructor|]. split;[exact Hsep|lia].
     * destruct(IH (byte::reversed) ltac:(discriminate) Hrun) as(payload & bad & Hinput & Hpayload & Hbad & Hlength).
       exists(byte::payload),bad. split;[cbn [app];now rewrite Hinput|]. split;[constructor;assumption|]. split;[exact Hbad|]. cbn [length] in *. lia.
Qed.
Theorem too_long input tail : read_token input=token_too_long tail ->
 exists prefix chars bad, input=prefix++chars++bad::tail /\
 Forall(fun ch=>separator ch=true)prefix /\ length chars=1024%nat /\
 Forall(fun ch=>separator ch=false)chars /\ separator bad=false.
Proof.
 unfold read_token. induction input as [|byte input IH];intro Hrun;[discriminate|].
 cbn [scan_token] in Hrun. destruct(separator byte) eqn:Hsep.
 - destruct(IH Hrun) as(prefix & chars & bad & Hinput & Hprefix & Hlength & Hchars & Hbad).
   exists(byte::prefix),chars,bad. split;[cbn [app];now rewrite Hinput|]. split;[constructor;assumption|]. repeat split;assumption.
 - destruct(started_long [byte] input tail ltac:(discriminate) Hrun) as(payload & bad & Hinput & Hpayload & Hbad & Hlength).
   exists [],(byte::payload),bad. cbn [app]. split;[now rewrite Hinput|]. split;[constructor|]. split;[cbn [length] in *;lia|].
   split;[constructor;assumption|exact Hbad].
Qed.
End ByteLexErrors.
