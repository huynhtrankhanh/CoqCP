From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternInvariant Intern.
From stdpp Require Import numbers list.

Open Scope Z_scope.

Module InternalObservation.
Section Effects.
Context {I : Type} {T : I -> Type} {V : Type}.
Definition local_flush (effect : WithLocalVariables I T V) :=
  match effect with DoWithArrays _ _ _ effect => isFlush effect | _ => False end.
Fixpoint local_nf {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) : Prop :=
  match code with
  | Done _ _ _ _ => True
  | Dispatch _ _ _ effect next => ~ local_flush effect /\ forall response, local_nf (next response)
  end.
Definition within_flush (effect : WithinLoop I T V) :=
  match effect with DoWithLocalVariables _ _ _ effect => local_flush effect | _ => False end.
Fixpoint within_nf {R} (code : Action (WithinLoop I T V) withinLoopReturnValue R) : Prop :=
  match code with
  | Done _ _ _ _ => True
  | Dispatch _ _ _ effect next => ~ within_flush effect /\ forall response, within_nf (next response)
  end.
Lemma local_bind {A B} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue A) next :
  local_nf code -> (forall value, local_nf (next value)) -> local_nf (R := B) (code >>= next).
Proof. induction code as [value|e cont IH]; [intros Hcode Hnext; apply Hnext|].
  intros [He Hcont] Hnext. split; [exact He|]. intro r. now apply IH. Qed.
Lemma within_bind {A B} (code : Action (WithinLoop I T V) withinLoopReturnValue A) next :
  within_nf code -> (forall value, within_nf (next value)) -> within_nf (R := B) (code >>= next).
Proof. induction code as [value|e cont IH]; [intros Hcode Hnext; apply Hnext|].
  intros [He Hcont] Hnext. split; [exact He|]. intro r. now apply IH. Qed.
Lemma lift_nf {R} (code : Action (WithArrays I T) withArraysReturnValue R) :
  NoFlush code -> local_nf (liftToWithLocalVariables (variableIndex := V) code).
Proof. induction code as [value|e cont IH]; [constructor|]. intros [He Hcont].
  cbn [liftToWithLocalVariables Action_rect local_nf]. split; [exact He|]. intro r. now apply IH. Qed.
Lemma within_lift_nf {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R) :
  local_nf code -> within_nf (liftToWithinLoop code).
Proof. induction code as [value|e cont IH]; [constructor|]. intros [He Hcont].
  cbn [liftToWithinLoop within_nf]. split; [exact He|]. intro r. now apply IH. Qed.
Lemma drop_nf (code : Action (WithinLoop I T V) withinLoopReturnValue unit) :
  within_nf code -> local_nf (dropWithinLoop code).
Proof.
  induction code as [value|e cont IH]; [constructor|]. intros [He Hcont].
  destruct e as [e| |]; cbn [dropWithinLoop Action_rect local_nf].
  - split; [exact He|]. intro r. now apply IH.
  - constructor.
  - constructor.
Qed.
Lemma loop_nf count (body : nat -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome) :
  (forall index, local_nf (body index)) -> local_nf (loop count body).
Proof. intro Hbody. induction count as [|count IH]; [constructor|]. rewrite loop_S.
  apply local_bind; [apply Hbody|]. intros []; [exact IH|constructor]. Qed.
Lemma tape_nf (body : Z -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome) :
  (forall ch, local_nf (body ch)) -> local_nf (tapeEnd body).
Proof.
  intro Hbody. unfold tapeEnd. split; [cbn [local_flush isFlush]; tauto|]. intro remaining.
  apply loop_nf. intro index. apply local_bind.
  - split; [cbn [local_flush isFlush]; tauto|]. intro ch. constructor.
  - intro ch. lazymatch goal with |- local_nf (if ?guard then _ else _) =>
    destruct guard; [constructor|apply Hbody] end.
Qed.
Context `{EqDecision V}.
Lemma eliminate_nf (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit) bs ns :
  local_nf code -> NoFlush (eliminateLocalVariables bs ns code).
Proof.
  induction code as [value|e cont IH] in bs, ns |- *; [constructor|]. intros [He Hcont].
  destruct e; cbn [eliminateLocalVariables NoFlush].
  - split; [exact He|]. intro r. now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
Qed.
End Effects.

Ltac array_nf :=
  match goal with
  | H : forall bs ns, NoFlush (?proc bs ns) |- NoFlush (?proc ?bs ?ns) => exact (H bs ns)
  end.
Ltac nf := first
  [ lazymatch goal with |- local_nf (Done _ _ _ _) => constructor end
  | lazymatch goal with |- within_nf (Done _ _ _ _) => constructor end
  | lazymatch goal with |- local_nf (bind _ _) => apply local_bind; [nf|intro; nf] end
  | lazymatch goal with |- within_nf (bind _ _) => apply within_bind; [nf|intro; nf] end
  | lazymatch goal with |- local_nf (liftToWithLocalVariables _) => apply lift_nf; array_nf end
  | lazymatch goal with |- within_nf (liftToWithinLoop _) => apply within_lift_nf; nf end
  | lazymatch goal with |- local_nf (dropWithinLoop _) => apply drop_nf; nf end
  | lazymatch goal with |- local_nf (loop _ _) => apply loop_nf; intro; nf end
  | lazymatch goal with |- local_nf (tapeEnd _) => apply tape_nf; intro; nf end
  | lazymatch goal with |- local_nf (if ?guard then _ else _) => destruct guard; nf end
  | lazymatch goal with |- within_nf (if ?guard then _ else _) => destruct guard; nf end
  | lazymatch goal with |- local_nf (Dispatch _ _ _ _ _) =>
      split; [cbn [local_flush isFlush]; tauto|intro; nf] end
  | lazymatch goal with |- within_nf (Dispatch _ _ _ _ _) =>
      split; [cbn [within_flush local_flush isFlush]; tauto|intro; nf] end
  | progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet
      retrieve store grow trap readChar shortCircuitAnd shortCircuitOr addInt subInt multInt
      andBits orBits xorBits shiftLeft shiftRight modIntUnsigned divIntUnsigned break continue]; nf
  | contradiction
  ].

Theorem sipRound_nf bs ns : NoFlush (funcdef_0__sipRound bs ns).
Proof. unfold funcdef_0__sipRound. apply eliminate_nf. unfold funcdef_0__sipRound_body. nf. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_nf bs ns : NoFlush (funcdef_0__sipWord bs ns).
Proof.
  pose proof sipRound_nf as Hround. unfold funcdef_0__sipWord. apply eliminate_nf. unfold funcdef_0__sipWord_body. nf.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_nf bs ns : NoFlush (funcdef_0__formulaHash bs ns).
Proof.
  pose proof sipRound_nf as Hround. pose proof sipWord_nf as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_nf. unfold funcdef_0__formulaHash_body. nf.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_nf bs ns : NoFlush (funcdef_0__rehashFormulas bs ns).
Proof.
  pose proof formulaHash_nf as Hhash. unfold funcdef_0__rehashFormulas.
  apply eliminate_nf. unfold funcdef_0__rehashFormulas_body. nf.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_nf bs ns : NoFlush (funcdef_0__intern bs ns).
Proof.
  pose proof formulaHash_nf as Hhash. pose proof rehash_nf as Hresize.
  unfold funcdef_0__intern. apply eliminate_nf. unfold funcdef_0__intern_body. nf.
Qed.

Local Opaque funcdef_0__intern.
Theorem push_nf bs ns : NoFlush (funcdef_0__push bs ns).
Proof.
  unfold funcdef_0__push. apply eliminate_nf. unfold funcdef_0__push_body. nf.
Qed.
Local Opaque funcdef_0__push.
Theorem tokenByte_nf bs ns : NoFlush (funcdef_0__tokenByte bs ns).
Proof.
  unfold funcdef_0__tokenByte. apply eliminate_nf. unfold funcdef_0__tokenByte_body. nf.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_nf bs ns : NoFlush (funcdef_0__readToken bs ns).
Proof.
  pose proof tokenByte_nf as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_nf. unfold funcdef_0__readToken_body. nf.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_nf bs ns : NoFlush (funcdef_0__readNat bs ns).
Proof.
  pose proof readToken_nf as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_nf. unfold funcdef_0__readNat_body. nf.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_nf bs ns : NoFlush (funcdef_0__lookup bs ns).
Proof.
  unfold funcdef_0__lookup. apply eliminate_nf. unfold funcdef_0__lookup_body. nf.
Qed.
Local Opaque funcdef_0__lookup.
Theorem renameIndex_nf bs ns : NoFlush (funcdef_0__renameIndex bs ns).
Proof.
  unfold funcdef_0__renameIndex. apply eliminate_nf. unfold funcdef_0__renameIndex_body. nf.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_nf bs ns : NoFlush (funcdef_0__renameCacheGet bs ns).
Proof. pose proof (formulaHash_nf) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_nf. unfold funcdef_0__renameCacheGet_body. nf. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_nf bs ns : NoFlush (funcdef_0__renameCacheGrow bs ns).
Proof. pose proof (formulaHash_nf) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_nf. unfold funcdef_0__renameCacheGrow_body. nf. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_nf bs ns : NoFlush (funcdef_0__renameCachePut bs ns).
Proof. pose proof (formulaHash_nf) as Hhash. pose proof (renameCacheGrow_nf) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_nf. unfold funcdef_0__renameCachePut_body. nf. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_nf bs ns : NoFlush (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_nf) as HrenameCacheGet.  pose proof (renameCachePut_nf) as HrenameCachePut.
  pose proof push_nf as Hdep0.
  pose proof renameIndex_nf as Hdep1.
  pose proof intern_nf as Hdep2.
  unfold funcdef_0__rename. apply eliminate_nf. unfold funcdef_0__rename_body. nf.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_nf bs ns : NoFlush (funcdef_0__predicate bs ns).
Proof.
  pose proof rename_nf as Hdep0.
  pose proof intern_nf as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_nf. unfold funcdef_0__predicate_body. nf.
Qed.
Local Opaque funcdef_0__predicate.
Theorem classEqual_nf bs ns : NoFlush (funcdef_0__classEqual bs ns).
Proof.
  pose proof predicate_nf as Hdep0.
  pose proof intern_nf as Hdep1.
  unfold funcdef_0__classEqual. apply eliminate_nf. unfold funcdef_0__classEqual_body. nf.
Qed.
Local Opaque funcdef_0__classEqual.
Theorem classMember_nf bs ns : NoFlush (funcdef_0__classMember bs ns).
Proof.
  pose proof rename_nf as Hdep0.
  pose proof predicate_nf as Hdep1.
  pose proof intern_nf as Hdep2.
  unfold funcdef_0__classMember. apply eliminate_nf. unfold funcdef_0__classMember_body. nf.
Qed.
Local Opaque funcdef_0__classMember.
Theorem setness_nf bs ns : NoFlush (funcdef_0__setness bs ns).
Proof.
  pose proof predicate_nf as Hdep0.
  pose proof intern_nf as Hdep1.
  unfold funcdef_0__setness. apply eliminate_nf. unfold funcdef_0__setness_body. nf.
Qed.
Local Opaque funcdef_0__setness.
Theorem axiom_nf bs ns : NoFlush (funcdef_0__axiom bs ns).
Proof.
  pose proof rename_nf as Hdep0.
  pose proof intern_nf as Hdep1.
  unfold funcdef_0__axiom. apply eliminate_nf. unfold funcdef_0__axiom_body. nf.
Qed.
Local Opaque funcdef_0__axiom.
Theorem schemaCheck_nf bs ns : NoFlush (funcdef_0__schemaCheck bs ns).
Proof.
  unfold funcdef_0__schemaCheck. apply eliminate_nf. unfold funcdef_0__schemaCheck_body. nf.
Qed.
Local Opaque funcdef_0__schemaCheck.
Theorem schemaClass_nf bs ns : NoFlush (funcdef_0__schemaClass bs ns).
Proof.
  unfold funcdef_0__schemaClass. apply eliminate_nf. unfold funcdef_0__schemaClass_body. nf.
Qed.
Local Opaque funcdef_0__schemaClass.
Theorem schemaShiftClass_nf bs ns : NoFlush (funcdef_0__schemaShiftClass bs ns).
Proof.
  pose proof schemaClass_nf as Hdep0.
  pose proof rename_nf as Hdep1.
  unfold funcdef_0__schemaShiftClass. apply eliminate_nf. unfold funcdef_0__schemaShiftClass_body. nf.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Theorem schemaMark_nf bs ns : NoFlush (funcdef_0__schemaMark bs ns).
Proof.
  unfold funcdef_0__schemaMark. apply eliminate_nf. unfold funcdef_0__schemaMark_body. nf.
Qed.
Local Opaque funcdef_0__schemaMark.
Theorem schemaInstance_nf bs ns : NoFlush (funcdef_0__schemaInstance bs ns).
Proof.
  pose proof schemaMark_nf as Hdep0.
  pose proof schemaShiftClass_nf as Hdep1.
  pose proof schemaClass_nf as Hdep2.
  pose proof classEqual_nf as Hdep3.
  pose proof classMember_nf as Hdep4.
  pose proof intern_nf as Hdep5.
  pose proof axiom_nf as Hdep6.
  unfold funcdef_0__schemaInstance. apply eliminate_nf. unfold funcdef_0__schemaInstance_body. nf.
Qed.
Local Opaque funcdef_0__schemaInstance.

Theorem generated_intern_observed s bs ns n observations :
  InternInvariant.table s n -> SipHashExecution.meta_value s 8 = 0%Z ->
  exists final, execObserved (funcdef_0__intern bs ns) (s,observations) = Some (tt,(final,observations)) /\
    InternExecution.logical_frame s final /\
    (SipHashExecution.meta_value final 8 <> 0%Z \/ InternExecution.canonical s final n
      (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b)).
Proof.
  intros Htable Hflag. destruct (InternExecution.generated_intern_correct s bs ns n Htable Hflag)
    as [final [Hrun Hpost]]. exists final. split; [|exact Hpost].
  now apply observed_plain; [apply intern_nf|].
Qed.
End InternalObservation.
