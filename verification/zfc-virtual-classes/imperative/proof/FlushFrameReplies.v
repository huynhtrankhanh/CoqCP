From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import FlushFrame InternalIO InternalIOProcedures ObservedLocal ReplyOK
 SchemaInstanceStorage SchemaInstanceHandler.
From stdpp Require Import numbers list.
From Stdlib Require Import Strings.String.

Module FlushFrameReplies.
Import FlushFrame.
Section Rules.
Context {I:Type} {T:I->Type} `{EqDecision I} {V:Type} `{EqDecision V}.
Lemma local_dispatch {R} (effect:WithLocalVariables I T V)
 (next:withLocalVariablesReturnValue effect->Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) :
 InternalIO.safe_local effect -> (forall response,local_closed(next response)) ->
 local_closed(Dispatch _ _ _ effect next).
Proof.
 intros Hsafe Hnext.
 change(local_closed ((Dispatch _ _ _ effect (fun response=>Done _ _ _ response))>>=next)).
 apply local_bind;[apply local_internal;split;[exact Hsafe|intro;constructor]|exact Hnext].
Qed.
End Rules.
Ltac closed := first
 [solve[apply local_internal;InternalIO.ro]
 |lazymatch goal with |-local_closed(bind _ _) => apply local_bind;[closed|intro;closed] end
 |lazymatch goal with |-local_closed(liftToWithLocalVariables _) => apply local_lift;closed end
 |lazymatch goal with |-local_closed(if ?guard then _ else _) => destruct guard;closed end
 |lazymatch goal with |-local_closed(Dispatch _ _ _ _ _) => apply local_dispatch;[cbn[InternalIO.safe_local InternalIO.safe_effect];tauto|intro;closed] end
 |match goal with H:forall bs ns,array_closed(?proc bs ns)|-array_closed(?proc ?bs ?ns)=>exact(H bs ns) end
 |solve[eauto with io_frames]
 |solve[apply array_internal;InternalIO.ro]
 |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet
      retrieve store grow trap readChar writeChar flush shortCircuitAnd shortCircuitOr addInt subInt multInt
      andBits orBits xorBits shiftLeft shiftRight modIntUnsigned divIntUnsigned break continue];closed].
Theorem ok bs ns : array_closed(funcdef_0__ok bs ns).
Proof.
 unfold funcdef_0__ok. apply eliminate,local_terminal_closed. rewrite ReplyOKExecution.actual_body.
 unfold ReplyOKExecution.body. apply local_prepend;intros []. apply local_prepend;intros [].
 apply local_prepend;intros []. apply local_flush_done.
Qed.
Local Opaque funcdef_0__ok.
Theorem no bs ns : array_closed(funcdef_0__no bs ns).
Proof.
 unfold funcdef_0__no. apply eliminate,local_terminal_closed. unfold funcdef_0__no_body.
 apply local_prepend;intros []. apply local_flush_done.
Qed.
Local Opaque funcdef_0__no.
Lemma lookup_io bs ns : InternalIO.array_ro(funcdef_0__lookup bs ns).
Proof. unfold funcdef_0__lookup. apply InternalIO.eliminate_ro. unfold funcdef_0__lookup_body. InternalIO.ro. Qed.
Local Opaque funcdef_0__lookup.
Theorem bindName bs ns : array_closed(funcdef_0__bindName bs ns).
Proof.
 pose proof ok as Hok. pose proof no as Hno. pose proof lookup_io as Hlookup.
 unfold funcdef_0__bindName. apply eliminate. unfold funcdef_0__bindName_body. closed.
Qed.
Local Opaque funcdef_0__bindName.
Theorem appendTheorem bs ns : array_closed(funcdef_0__appendTheorem bs ns).
Proof.
 pose proof ok as Hok. pose proof no as Hno.
 unfold funcdef_0__appendTheorem. apply eliminate. unfold funcdef_0__appendTheorem_body. closed.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem schema_suffix : local_closed SchemaInstanceHandler.suffix.
Proof.
 pose proof ok as Hok. pose proof no as Hno. pose proof appendTheorem as Happend.
 pose proof SchemaInstanceStorage.io as Hinstance.
 unfold SchemaInstanceHandler.suffix. closed.
Qed.
End FlushFrameReplies.
