From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia Logic.Eqdep_dec.
Section Pointwise.
Context {I:Type} {T:I->Type} `{EqDecision I}.
Definition same (s t:@Machine I T) : Prop :=
 stdin s=stdin t /\ stdout s=stdout t /\ forall name,memory s name=memory t name.
Lemma same_modify s t name index (value:T name) : same s t ->
 same (withMemory s (modifyArray (memory s) name index value))
      (withMemory t (modifyArray (memory t) name index value)).
Proof.
 intros (Hin & Hout & Hmem). split;[exact Hin|]. split;[exact Hout|].
 intro watched. change (modifyArray (memory s) name index value watched = modifyArray (memory t) name index value watched). unfold modifyArray.
 destruct (decide (watched=name)) as [Heq|Hne].
 - destruct Heq. cbn. now rewrite Hmem.
 - exact (Hmem watched).
Qed.
Lemma same_grow s t name size (zero:T name) : same s t ->
 same (withMemory s (growArrays (memory s) name size zero))
      (withMemory t (growArrays (memory t) name size zero)).
Proof.
 intros (Hin & Hout & Hmem). split;[exact Hin|]. split;[exact Hout|].
 intro watched. change (growArrays (memory s) name size zero watched = growArrays (memory t) name size zero watched). unfold growArrays.
 destruct (decide (watched=name)) as [Heq|Hne].
 - destruct Heq. cbn. now rewrite Hmem.
 - exact (Hmem watched).
Qed.

Lemma same_input s t input : same s t -> same (withInput s input) (withInput t input).
Proof. intros (_ & Hout & Hmem). split;[reflexivity|]. split;assumption. Qed.
Lemma same_output s t output : same s t -> same (withOutput s output) (withOutput t output).
Proof. intros (Hin & _ & Hmem). split;[exact Hin|]. split;[reflexivity|exact Hmem]. Qed.
Theorem step_same (effect:WithArrays I T) s t : same s t ->
 match step effect s,step effect t with
 | Some (result1,after),Some (result2,next)=>result1=result2 /\ same after next
 | None,None=>True | _,_=>False end.
Proof.
 intro Hsame. destruct Hsame as (Hin & Hout & Hmem).
 assert (Hsame:same s t) by (repeat split;assumption).
 destruct effect as [basic|name index|name index value|name size zero].
 - destruct basic; cbn [step].
   + constructor.
   + split;[reflexivity|exact Hsame].
   + rewrite <-Hin. destruct(stdin s) as [|ch tail];cbn;split;try reflexivity;try exact Hsame;now apply same_input.
   + split;[reflexivity|]. rewrite <-Hout. now apply same_output.
   + rewrite <-Hin. split;[reflexivity|exact Hsame].
 - cbn [step]. rewrite <- (Hmem name). destruct (decide (Nat.lt (Z.to_nat index) (length (memory s name))));cbn.
   + split;[reflexivity|exact Hsame].
   + constructor.
 - cbn [step]. rewrite <- (Hmem name). destruct (decide (Nat.lt (Z.to_nat index) (length (memory s name))));cbn.
   + split;[reflexivity|]. now apply same_modify.
   + constructor.
 - cbn [step]. split;[reflexivity|]. now apply same_grow.
Qed.

Theorem observed_same {R} (code:Action (WithArrays I T) withArraysReturnValue R) s t observations :
 same s t ->
 match execObserved code (s,observations),execObserved code (t,observations) with
 | Some (r1,(after,trace1)),Some (r2,(next,trace2))=>r1=r2 /\ trace1=trace2 /\ same after next
 | None,None=>True | _,_=>False end.
Proof.
 induction code as [value|effect continuation IH] in s,t,observations|-*; intro Hsame.
 - cbn [execObserved]. split;[reflexivity|]. split;[reflexivity|exact Hsame].
 - cbn [execObserved]. unfold observedStep. cbn [fst snd].
   pose proof (step_same effect s t Hsame) as Hstep.
   destruct (step effect s) as [[response after]|] eqn:Hleft;
   destruct (step effect t) as [[response2 next]|] eqn:Hright;
   cbn in Hstep|-*;try contradiction;try constructor.
   destruct Hstep as [Hresponse Hstates]. subst response2.
   destruct Hsame as (Hin & Hout & Hmem).
   assert (Htrace:(match effect with DoBasicEffect _ _ Flush=>observations++[{|flushedOutput:=stdout s;unreadInput:=stdin s|}]|_=>observations end)=
      (match effect with DoBasicEffect _ _ Flush=>observations++[{|flushedOutput:=stdout t;unreadInput:=stdin t|}]|_=>observations end)).
   { destruct effect as [basic|name index|name index value|name size zero];try reflexivity.
     destruct basic;try reflexivity. now rewrite Hin,Hout. }
   rewrite Htrace. apply IH. exact Hstates.
Qed.
End Pointwise.
