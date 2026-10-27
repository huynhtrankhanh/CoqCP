From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From NativeProof Require Import InternalIO ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List.

Module FlushFrame.
Definition latest (events:list FlushSnapshot) (initial:FlushSnapshot) := List.last events initial.
Lemma latest_nonempty events initial other : events<>[] -> latest events initial=latest events other.
Proof.
 unfold latest. induction events as [|x events IH];[contradiction|].
 intros _. destruct events as [|y events];[reflexivity|]. now apply IH.
Qed.
Lemma latest_append xs ys initial : latest (xs++ys) initial=latest ys (latest xs initial).
Proof.
 unfold latest. induction xs as [|x xs IH] in initial |- *; [reflexivity|].
 destruct xs as [|x' xs].
 - destruct ys as [|y ys];[reflexivity|]. change(latest (y::ys) initial=latest (y::ys) x).
   apply latest_nonempty;discriminate.
 - apply IH.
Qed.
Section Machines.
Context {I:Type} {T:I->Type} `{EqDecision I}.
Definition checkpoint (s:@Machine I T) := {|flushedOutput:=stdout s;unreadInput:=stdin s|}.
Definition post before observations after trace := exists emitted,
 trace=observations++emitted /\ checkpoint after=latest emitted (checkpoint before).
Definition terminal before observations after trace := exists emitted,
 trace=observations++emitted /\ emitted<>[] /\ checkpoint after=latest emitted (checkpoint before).
Lemma post_same before observations after : checkpoint after=checkpoint before -> post before observations after observations.
Proof. intro Hsame. exists [];split;[now rewrite app_nil_r|exact Hsame]. Qed.
Lemma post_trans before observations middle trace after finaltrace :
 post before observations middle trace -> post middle trace after finaltrace -> post before observations after finaltrace.
Proof.
 intros [xs [Htrace Hmiddle]] [ys [Hfinal Hafter]]. exists(xs++ys). split.
 - rewrite Hfinal,Htrace. now rewrite <-app_assoc.
 - rewrite latest_append. now rewrite <-Hmiddle.
Qed.
Lemma terminal_post before observations after trace : terminal before observations after trace -> post before observations after trace.
Proof. intros [events [Htrace [Hnonempty Hafter]]]. now exists events. Qed.
Lemma prepend_terminal before observations middle trace after finaltrace :
 (exists prefix,trace=observations++prefix) -> terminal middle trace after finaltrace -> terminal before observations after finaltrace.
Proof.
 intros [prefix Hprefix] [events [Htrace [Hnonempty Hafter]]]. exists(prefix++events). split.
 - rewrite Htrace,Hprefix. now rewrite <-app_assoc.
 - split;[intro Hnil;apply app_eq_nil in Hnil;tauto|].
   rewrite latest_append. rewrite (latest_nonempty events (latest prefix (checkpoint before)) (checkpoint middle) Hnonempty).
   exact Hafter.
Qed.
Theorem singleton before observations after event :
 post before observations after (observations++[event]) -> checkpoint after=event.
Proof. intros [events [Htrace Hafter]]. apply app_inv_head in Htrace. subst events. exact Hafter. Qed.
Definition array_closed {R} (code:Action (WithArrays I T) withArraysReturnValue R) :=
 forall s observations value after trace,
 execObserved code (s,observations)=Some(value,(after,trace)) -> post s observations after trace.
Lemma step_suffix (effect:WithArrays I T) s observations value after trace :
 observedStep effect (s,observations)=Some(value,(after,trace)) -> exists emitted,trace=observations++emitted.
Proof.
 unfold observedStep. cbn [fst snd]. destruct(step effect s) as [[response next]|] eqn:Hstep;[|discriminate].
 cbn [optionBind fst snd]. intro Hrun. injection Hrun as _ _ <-.
 destruct effect as [basic|name slot|name slot item|name size zero];try (exists [];now rewrite app_nil_r).
 destruct basic;try (exists [];now rewrite app_nil_r). now exists [checkpoint s].
Qed.
Theorem array_suffix {R} (code:Action (WithArrays I T) withArraysReturnValue R) s observations value after trace :
 execObserved code (s,observations)=Some(value,(after,trace)) -> exists emitted,trace=observations++emitted.
Proof.
 induction code as [x|effect next IH] in s,observations |- *.
 - intro Hrun. injection Hrun as _ _ <-. exists [];now rewrite app_nil_r.
 - cbn [execObserved]. destruct(observedStep effect(s,observations)) as [[response [middle events]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd]. intro Hrun. destruct(IH response middle events Hrun) as [ys Hys].
   destruct(step_suffix _ _ _ _ _ _ Hstep) as [xs Hxs]. exists(xs++ys). rewrite Hys,Hxs. now rewrite <-app_assoc.
Qed.
Lemma safe_step (effect:WithArrays I T) s observations value after trace :
 InternalIO.safe_effect effect -> observedStep effect(s,observations)=Some(value,(after,trace)) -> post s observations after trace.
Proof.
 intros Hsafe Hrun. assert(Hplain:step effect s=Some(value,after)).
 { unfold observedStep in Hrun. cbn [fst snd] in Hrun. destruct(step effect s) as [[r next]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun. injection Hrun as -> -> _. reflexivity. }
 destruct(InternalIO.step_preserves _ _ _ _ Hsafe Hplain) as [Hin Hout].
 assert(Hcheckpoint:checkpoint after=checkpoint s) by (unfold checkpoint;now rewrite Hin,Hout).
 unfold observedStep in Hrun. cbn [fst snd] in Hrun. rewrite Hplain in Hrun. cbn [optionBind fst snd] in Hrun.
 destruct effect as [basic|name slot|name slot item|name size zero];
 try (inversion Hrun;subst trace;apply post_same;exact Hcheckpoint).
 destruct basic;try (inversion Hrun;subst trace;apply post_same;exact Hcheckpoint);try contradiction.
 inversion Hrun;subst trace. exists [checkpoint s]. split;[reflexivity|exact Hcheckpoint].
Qed.
Theorem array_internal {R} (code:Action (WithArrays I T) withArraysReturnValue R) : InternalIO.array_ro code -> array_closed code.
Proof.
 induction code as [x|effect next IH]; intros Hro s observations value after trace Hrun.
 - injection Hrun as _ <- <-. apply post_same;reflexivity.
 - destruct Hro as [Hsafe Hnext]. cbn [execObserved] in Hrun.
   destruct(observedStep effect(s,observations)) as [[response [middle events]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun.
   exact(post_trans _ _ _ _ _ _ (safe_step _ _ _ _ _ _ Hsafe Hstep) (IH response (Hnext response) middle events value after trace Hrun)).
Qed.
Context {V:Type} `{EqDecision V}.
Definition local_closed {R} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) :=
 forall f observations value after trace,
 ObservedLocal.execLocalObserved code(f,observations)=Some(value,(after,trace)) -> post(machine f) observations(machine after) trace.
Definition local_terminal {R} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) :=
 forall f observations value after trace,
 ObservedLocal.execLocalObserved code(f,observations)=Some(value,(after,trace)) -> terminal(machine f) observations(machine after) trace.
Lemma local_step_suffix (effect:WithLocalVariables I T V) f observations value after trace :
 ObservedLocal.localStepObserved effect(f,observations)=Some(value,(after,trace)) -> exists emitted,trace=observations++emitted.
Proof.
 destruct effect as [arrayeffect|name|name item|name|name item];cbn [ObservedLocal.localStepObserved fst snd];
 try (intro Hrun;injection Hrun as _ _ <-;exists [];now rewrite app_nil_r).
 destruct(observedStep arrayeffect (machine f,observations)) as [[response [middle events]]|] eqn:Hstep;[|discriminate].
 cbn [optionBind fst snd]. intro Hrun. injection Hrun as _ _ <-. exact(step_suffix _ _ _ _ _ _ Hstep).
Qed.
Theorem local_suffix {R} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) f observations value after trace :
 ObservedLocal.execLocalObserved code(f,observations)=Some(value,(after,trace)) -> exists emitted,trace=observations++emitted.
Proof.
 induction code as [x|effect next IH] in f,observations |- *.
 - intro Hrun. injection Hrun as _ _ <-. exists [];now rewrite app_nil_r.
 - cbn [ObservedLocal.execLocalObserved]. destruct(ObservedLocal.localStepObserved effect(f,observations)) as [[response [middle events]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd]. intro Hrun. destruct(IH response middle events Hrun) as [ys Hys].
   destruct(local_step_suffix _ _ _ _ _ _ Hstep) as [xs Hxs]. exists(xs++ys). rewrite Hys,Hxs. now rewrite <-app_assoc.
Qed.
Lemma local_bind {A B} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue A) next :
 local_closed code -> (forall value,local_closed (R:=B) (next value)) -> local_closed(code>>=next).
Proof.
 intros Hcode Hnext f observations value after trace Hrun. rewrite ObservedLocal.local_bind in Hrun.
 destruct(ObservedLocal.execLocalObserved code(f,observations)) as [[response [middle events]]|] eqn:Hfirst;[|discriminate].
 cbn [optionBind fst snd] in Hrun. exact(post_trans _ _ _ _ _ _ (Hcode _ _ _ _ _ Hfirst) (Hnext _ _ _ _ _ _ Hrun)).
Qed.
Lemma local_prepend {A B} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue A) next :
 (forall value,local_terminal (R:=B) (next value)) -> local_terminal(code>>=next).
Proof.
 intros Hnext f observations value after trace Hrun. rewrite ObservedLocal.local_bind in Hrun.
 destruct(ObservedLocal.execLocalObserved code(f,observations)) as [[response [middle events]]|] eqn:Hfirst;[|discriminate].
 cbn [optionBind fst snd] in Hrun. exact(prepend_terminal _ _ _ _ _ _ (local_suffix _ _ _ _ _ _ Hfirst) (Hnext _ _ _ _ _ _ Hrun)).
Qed.
Lemma local_terminal_closed {R} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) : local_terminal code -> local_closed code.
Proof. intros Hcode f observations value after trace Hrun. now apply terminal_post, (Hcode _ _ _ _ _ Hrun). Qed.
Lemma local_flush_done : local_terminal (flush I T V >>= fun _=>Done _ _ _ tt).
Proof.
 intros f observations value after trace Hrun.
 cbn [flush bind ObservedLocal.execLocalObserved ObservedLocal.localStepObserved observedStep step optionBind fst snd] in Hrun.
 injection Hrun as _ <- <-. exists [checkpoint(machine f)]. split;[reflexivity|]. split;[discriminate|reflexivity].
Qed.
Lemma local_lift {R} (code:Action (WithArrays I T) withArraysReturnValue R) : array_closed code -> local_closed(liftToWithLocalVariables code).
Proof.
 intros Hcode f observations value after trace Hrun. rewrite ObservedLocal.lift_correct in Hrun.
 destruct(execObserved code(machine f,observations)) as [[response [middle events]]|] eqn:Hfirst;[|discriminate].
 cbn [optionBind fst snd] in Hrun. injection Hrun as _ <- <-. exact(Hcode _ _ _ _ _ Hfirst).
Qed.
Theorem local_internal {R} (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) : InternalIO.local_ro code -> local_closed code.
Proof.
 induction code as [x|effect next IH];intros Hro f observations value after trace Hrun.
 - injection Hrun as _ <- <-. apply post_same;reflexivity.
 - destruct Hro as [Hsafe Hnext]. cbn [ObservedLocal.execLocalObserved] in Hrun.
   destruct(ObservedLocal.localStepObserved effect(f,observations)) as [[response [middle events]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun. eapply post_trans;[|exact(IH response (Hnext response) _ _ _ _ _ Hrun)].
   destruct effect as [arrayeffect|name|name item|name|name item];cbn [ObservedLocal.localStepObserved fst snd] in Hstep;
   try (injection Hstep as _ <- <-;apply post_same;reflexivity).
   destruct(observedStep arrayeffect (machine f,observations)) as [[r [s events']]|] eqn:Harray;[|discriminate].
   cbn [optionBind fst snd] in Hstep. injection Hstep as _ <- <-. exact(safe_step _ _ _ _ _ _ Hsafe Harray).
Qed.
Theorem eliminate (code:Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit) bs ns :
 local_closed code -> array_closed(eliminateLocalVariables bs ns code).
Proof.
 intros Hcode s observations value after trace Hrun. rewrite ObservedLocal.eliminate_correct in Hrun.
 destruct(ObservedLocal.execLocalObserved code({|machine:=s;bools:=bs;nums:=ns|},observations)) as [[response [middle events]]|] eqn:Hfirst;[|discriminate].
 cbn [optionBind fst snd] in Hrun. injection Hrun as _ <- <-. exact(Hcode _ _ _ _ _ Hfirst).
Qed.
End Machines.
End FlushFrame.
