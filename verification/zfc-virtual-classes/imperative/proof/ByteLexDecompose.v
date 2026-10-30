From CoqCP Require Import Options.
From Trusted Require Import ByteProtocol.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ByteLexDecompose.
Import ByteProtocol.
Lemma started_token reversed input chars tail ended :
 reversed<>[] -> scan_token reversed input=token chars tail ended ->
 exists payload, chars=rev reversed++payload /\ Forall(fun ch=>separator ch=false)payload /\
 ((ended=true /\ tail=[] /\ input=payload) \/
  (ended=false /\ exists sep, separator sep=true /\ input=payload++sep::tail)).
Proof.
 induction input as [|byte input IH] in reversed|-*;intros Hnonempty Hrun.
 - cbn [scan_token] in Hrun. destruct reversed as [|head rest];[contradiction|].
   inversion Hrun;subst. exists []. rewrite app_nil_r. split;[reflexivity|]. split;[constructor|]. left. repeat split;reflexivity.
 - cbn [scan_token] in Hrun. destruct(separator byte) eqn:Hsep.
   + destruct reversed as [|head rest];[contradiction|]. inversion Hrun;subst.
     exists []. rewrite app_nil_r. split;[reflexivity|]. split;[constructor|]. right.
     split;[reflexivity|]. exists byte. split;[exact Hsep|reflexivity].
   + destruct(Nat.eqb(length reversed)1024) eqn:Hlimit;[discriminate|].
     destruct(IH (byte::reversed) ltac:(discriminate) Hrun) as(payload & Hchars & Hpayload & Hending).
     exists(byte::payload). split.
     * rewrite Hchars. cbn [rev]. rewrite <-app_assoc. reflexivity.
     * split;[constructor;assumption|]. destruct Hending as [[-> [-> ->]]|[-> [sep [Hseparator Hinput]]]].
       -- left. repeat split;reflexivity.
       -- right. split;[reflexivity|]. exists sep. split;[exact Hseparator|]. now cbn [app];rewrite Hinput.
Qed.
Theorem token input chars tail ended : read_token input=token chars tail ended ->
 exists prefix payload, Forall(fun ch=>separator ch=true)prefix /\ chars=payload /\
 Forall(fun ch=>separator ch=false)payload /\ payload<>[] /\
 ((ended=true /\ tail=[] /\ input=prefix++payload) \/
  (ended=false /\ exists sep,separator sep=true /\ input=prefix++payload++sep::tail)).
Proof.
 unfold read_token. induction input as [|byte input IH];intro Hrun;[discriminate|].
 cbn [scan_token] in Hrun. destruct(separator byte) eqn:Hsep.
 - destruct(IH Hrun) as(prefix & payload & Hprefix & Hchars & Hpayload & Hnonempty & Hending).
   exists(byte::prefix),payload. split;[constructor;assumption|]. split;[exact Hchars|]. split;[exact Hpayload|]. split;[exact Hnonempty|].
   destruct Hending as [[-> [-> ->]]|[-> [sep [Hseparator Hinput]]]].
   + left. repeat split;reflexivity.
   + right. split;[reflexivity|]. exists sep. split;[exact Hseparator|]. cbn [app]. now rewrite Hinput.
 - destruct(started_token [byte] input chars tail ended ltac:(discriminate) Hrun) as(payload & Hchars & Hpayload & Hending).
   exists [],(byte::payload). split;[constructor|]. split.
   + cbn [rev app] in Hchars. exact Hchars.
   + split;[constructor;assumption|]. split;[discriminate|].
     destruct Hending as [[-> [-> ->]]|[-> [sep [Hseparator Hinput]]]].
     * left. repeat split;reflexivity.
     * right. split;[reflexivity|]. exists sep. split;[exact Hseparator|]. cbn [app]. now rewrite Hinput.
Qed.
End ByteLexDecompose.
