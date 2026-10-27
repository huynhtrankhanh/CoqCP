From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Lift HashTable FormulaEncoding Representation FormulaTopology
 RenameStack RenameMemoIndexBounds RenameMemoInput Intern InternBounded InternReserve Observation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexBounds.
Import IndexExecution SipHashExecution IndexSemantics.
Definition raw_arena native count bound := forall node,(node<count)%nat ->
 RenameMemoInput.raw_bound bound (HashTableInvariant.tuple_at native node).
Definition formulas bound fs := Forall (RenameMemoIndexBounds.formula_bound bound) fs.
Definition class_bound bound cls := match cls with
 | VirtualClasses.set variable=>(variable<=bound)%nat
 | VirtualClasses.abstract p=>RenameMemoIndexBounds.formula_bound bound (VirtualClasses.erase p)
 end.
Definition classes bound entries := Forall (class_bound bound) entries.
Lemma formula_mono lower upper p : (lower<=upper)%nat ->
 RenameMemoIndexBounds.formula_bound lower p -> RenameMemoIndexBounds.formula_bound upper p.
Proof.
 intro Hle. induction p as [|i j|i j|p IHp q IHq|p IHp];cbn [RenameMemoIndexBounds.formula_bound];intuition lia.
Qed.
Lemma formulas_mono lower upper fs : (lower<=upper)%nat -> formulas lower fs -> formulas upper fs.
Proof. intros Hle Hfs. induction Hfs;constructor;[eapply formula_mono;eassumption|assumption]. Qed.
Lemma formula_lookup bound fs index p : formulas bound fs -> nth_error fs index=Some p ->
 RenameMemoIndexBounds.formula_bound bound p.
Proof.
 intros Hfs. induction Hfs as [|head tail Hhead Htail IH] in index|-*;[destruct index;discriminate|].
 destruct index as [|index];[intro H;injection H as <-;exact Hhead|apply IH].
Qed.
Lemma formulas_of_lookup bound fs :
 (forall index p,nth_error fs index=Some p -> RenameMemoIndexBounds.formula_bound bound p) -> formulas bound fs.
Proof.
 intro Hlookup. induction fs as [|head tail IH];constructor.
 - exact (Hlookup 0%nat head eq_refl).
 - apply IH. intros index p Hindex. exact (Hlookup (S index) p Hindex).
Qed.
Lemma raw_arena_mono native count lower upper : (lower<=upper)%nat ->
 raw_arena native count lower -> raw_arena native count upper.
Proof. intros Hle Hraw node Hnode. eapply RenameMemoInput.raw_bound_monotone;[apply Hraw;exact Hnode|exact Hle]. Qed.
Lemma raw_arena_prefix native first last bound : (first<=last)%nat ->
 raw_arena native last bound -> raw_arena native first bound.
Proof. intros Hle Hraw node Hnode. apply Hraw;lia. Qed.
Lemma raw_index_max_bound raw bound : RenameMemoInput.raw_bound bound raw ->
 (RenameMemoInput.raw_index_max raw<=bound)%nat.
Proof.
 destruct raw as [[tag a] b]. unfold RenameMemoInput.raw_index_max,RenameMemoInput.raw_bound.
 cbn beta iota zeta. intro Hraw. destruct (BinInt.Z.eq_dec tag 1) as [H1|H1].
 - subst tag. destruct (Hraw (or_introl eq_refl)) as [Ha Hb]. apply Nat.max_lub;assumption.
 - destruct (BinInt.Z.eq_dec tag 2) as [H2|H2].
   + subst tag. destruct (Hraw (or_intror eq_refl)) as [Ha Hb]. apply Nat.max_lub;assumption.
   + lia.
Qed.
Lemma indices_max_bound native count bound : raw_arena native count bound ->
 (RenameMemoInput.indices_max native count<=bound)%nat.
Proof.
 induction count as [|count IH];[cbn;lia|]. intro Hraw. cbn [RenameMemoInput.indices_max].
 apply Nat.max_lub.
 - apply IH. apply raw_arena_prefix with (last:=S count);[lia|exact Hraw].
 - apply raw_index_max_bound. apply Hraw;lia.
Qed.
Lemma raw_arena_computed native count : raw_arena native count (RenameMemoInput.indices_max native count).
Proof. intros node Hnode. exact (RenameMemoInput.stored_index_bound native count node Hnode). Qed.
Theorem raw_arena_iff_max native count bound : raw_arena native count bound <->
 (RenameMemoInput.indices_max native count<=bound)%nat.
Proof. split;[apply indices_max_bound|intro Hle;eapply raw_arena_mono;[exact Hle|apply raw_arena_computed]]. Qed.
Lemma decoded_raw_bound fs raw bound p : FormulaEncoding.decode fs raw=Some p ->
 RenameMemoIndexBounds.formula_bound bound p -> RenameMemoInput.raw_bound bound raw.
Proof.
 destruct raw as [[tag a] b]. unfold RenameMemoInput.raw_bound.
 intros Hdecode Hp [Htag|Htag];subst tag;cbn [FormulaEncoding.decode] in Hdecode;injection Hdecode as <-;exact Hp.
Qed.
Theorem canonical_formulas_raw native fs bound : NativeRepresentation.canonical_arena native fs ->
 formulas bound fs -> raw_arena native (length fs) bound.
Proof.
 intros Harena Hfs node Hnode. destruct (nth_error fs node) as [p|] eqn:Hlookup;[|apply nth_error_None in Hlookup;lia].
 eapply decoded_raw_bound.
 - exact (NativeRepresentation.represented_lookup native fs node p (proj1 (proj2 Harena)) Hlookup).
 - exact (formula_lookup bound fs node p Hfs Hlookup).
Qed.
Theorem canonical_raw_formulas native fs bound : NativeRepresentation.canonical_arena native fs ->
 FormulaTopology.ordered native (length fs) -> raw_arena native (length fs) bound -> formulas bound fs.
Proof.
 intros Harena Htop Hraw. apply formulas_of_lookup. intros index p Hlookup.
 assert (Hinput:RenameMemoInput.input_bound native index bound).
 { intros node Hnode. apply Hraw. assert (index<length fs)%nat by (apply nth_error_Some;congruence). lia. }
 exact (proj1 (RenameMemoInput.canonical_source_bounds native fs index bound p Harena Htop Hlookup Hinput)).
Qed.
Lemma raw_array_frame before after count bound : memory after arraydef_0__formulas=memory before arraydef_0__formulas ->
 raw_arena before count bound -> raw_arena after count bound.
Proof. intros Harray Hraw node Hnode. unfold HashTableInvariant.tuple_at. rewrite Harray. exact (Hraw node Hnode). Qed.
Lemma intern_canonical before after count raw bound : InternExecution.canonical before after count raw ->
 raw_arena before count bound -> RenameMemoInput.raw_bound bound raw ->
 raw_arena after (Z.to_nat (meta_value after 1)) bound.
Proof.
 intros [Herror [nextCount [index [Hshape [Htable [Hindex [Hresult [Hraw Hprefix]]]]]]]] Hbefore Hbound.
 pose proof (proj1 (proj2 Htable)) as Hcount. rewrite Hcount,Nat2Z.id.
 destruct Hshape as [->|[-> ->]];intros node Hnode.
 - rewrite Hprefix by exact Hnode. exact (Hbefore node Hnode).
 - destruct (Nat.eq_dec node count) as [->|Hother];[now rewrite Hraw|].
   rewrite Hprefix by lia. apply Hbefore;lia.
Qed.
Theorem observed_intern before after bs ns fs next bound observations trace :
 NativeRepresentation.canonical_arena before fs -> meta_value before 8=0 ->
 Z.of_nat (length fs)<=9223372036854775807 -> raw_arena before (length fs) bound ->
 RenameMemoInput.raw_bound bound (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
 execObserved (funcdef_0__intern bs ns) (before,observations)=Some(tt,(after,trace)) ->
 NativeRepresentation.canonical_arena after next -> raw_arena after (length next) bound.
Proof.
 intros Harena Herror Hcapacity Hindices Hraw Hrun Hnext.
 destruct (InternBounded.generated_intern_bounded before bs ns (length fs) (proj1 Harena) Herror Hcapacity)
 as (actual & Hactual & Hframe & Hcanonical).
 assert (Hobserved:execObserved (funcdef_0__intern bs ns) (before,observations)=Some(tt,(actual,observations))).
 { apply observed_plain;[apply InternalObservation.intern_nf|exact Hactual]. }
 rewrite Hrun in Hobserved. injection Hobserved as Hafter Htrace. subst actual.
 pose proof (intern_canonical before after (length fs) _ bound Hcanonical Hindices Hraw) as Hbound.
 pose proof (proj1 (proj2 (proj1 Hnext))) as Hcount. rewrite Hcount,Nat2Z.id in Hbound. exact Hbound.
Qed.
Theorem generated_intern before bs ns fs p reserve bound observations :
 NativeRepresentation.canonical_arena before fs -> meta_value before 8=0 ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 -> raw_arena before (length fs) bound ->
 RenameMemoInput.raw_bound bound (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
 FormulaEncoding.normal (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
 FormulaEncoding.decode fs (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b)=Some p ->
 exists after next index,
 execObserved (funcdef_0__intern bs ns) (before,observations)=Some(tt,(after,observations)) /\
 InternExecution.logical_frame before after /\ NativeRepresentation.canonical_arena after next /\
 meta_value after 8=0 /\ meta_value after 0=Z.of_nat index /\ word (Z.of_nat index) /\
 nth_error next index=Some p /\ (exists extra,next=fs++extra) /\
 Z.of_nat (length next+reserve)<=9223372036854775807 /\ raw_arena after (length next) bound.
Proof.
 intros Harena Herror Hcapacity Hindices Hraw Hnormal Hdecode.
 destruct (InternReserve.generated_refines before bs ns fs p reserve observations Harena Herror Hcapacity Hnormal Hdecode)
 as (after & next & index & Hrun & Hframe & Hnext & Hclear & Hindex & Hword & Hlookup & Hprefix & Hroom).
 exists after,next,index. repeat first [assumption|split].
 exact (observed_intern before after bs ns fs next bound observations observations Harena Herror ltac:(lia) Hindices Hraw Hrun Hnext).
Qed.
Theorem renamed_formula bound m shift arg depth p : RenameMemoIndexBounds.formula_bound bound p ->
 RenameMemoIndexBounds.formula_bound (bound+RenameMemoIndexBounds.increment m shift arg)
   (RenameStack.renamed (renaming m shift arg) depth p).
Proof.
 induction p as [|i j|i j|p IHp q IHq|p IHp] in depth|-*;unfold RenameStack.renamed in *;
 cbn [SetTheory.rename RenameMemoIndexBounds.formula_bound];try tauto.
 - intros [Hi Hj]. pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg i).
   pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg j). split;lia.
 - intros [Hi Hj]. pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg i).
   pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg j). split;lia.
 - intros [Hp Hq]. split;[exact (IHp depth Hp)|exact (IHq depth Hq)].
 - exact (IHp (S depth)).
Qed.
End SchemaEvaluationIndexBounds.
