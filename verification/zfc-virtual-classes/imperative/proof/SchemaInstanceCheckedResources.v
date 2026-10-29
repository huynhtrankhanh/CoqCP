From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash Representation SchemaRepresentation SchemaGraph SchemaMetadata SchemaMarking SchemaNodeMeaning
 SchemaEvaluationIndexBounds RenameMemoIndexBounds SchemaEvaluationIndexCell SchemaEvaluationIndexSchedule
 SchemaInstanceGeneralReady SchemaInstanceGeneralProtocol SchemaInstanceGeneralCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaInstanceCheckedResources.
Import IndexExecution SipHashExecution.
Fixpoint formula_max p := match p with
 | SetTheory.falsity=>0%nat
 | SetTheory.equal i j | SetTheory.member i j=>Nat.max i j
 | SetTheory.implies p q=>Nat.max (formula_max p) (formula_max q)
 | SetTheory.all p=>formula_max p end.
Fixpoint formulas_max entries := match entries with
 | []=>0%nat | p::tail=>Nat.max (formula_max p) (formulas_max tail) end.
Definition class_max cls := match cls with
 | VirtualClasses.set variable=>variable
 | VirtualClasses.abstract body=>formula_max (VirtualClasses.erase body) end.
Fixpoint classes_max entries := match entries with
 | []=>0%nat | cls::tail=>Nat.max (class_max cls) (classes_max tail) end.
Definition initial_bound logical := Nat.max (formulas_max (Protocol.formulas logical)) (classes_max (Protocol.classes logical)).
Lemma formula_bound p bound : (formula_max p<=bound)%nat -> RenameMemoIndexBounds.formula_bound bound p.
Proof.
 induction p as [|i j|i j|p IH q JH|p IH];cbn [formula_max RenameMemoIndexBounds.formula_bound];intro H;
 try exact I;try (split;lia);try (split;[apply IH|apply JH];lia);apply IH;exact H.
Qed.
Lemma formulas_bound entries bound : (formulas_max entries<=bound)%nat -> SchemaEvaluationIndexBounds.formulas bound entries.
Proof.
 induction entries as [|p tail IH];cbn [formulas_max];intro H;[constructor|].
 constructor;[apply formula_bound;lia|apply IH;lia].
Qed.
Lemma class_bound cls bound : (class_max cls<=bound)%nat -> SchemaEvaluationIndexBounds.class_bound bound cls.
Proof. destruct cls;cbn [class_max SchemaEvaluationIndexBounds.class_bound];intro H;[exact H|exact (formula_bound _ bound H)]. Qed.
Lemma classes_bound entries bound : (classes_max entries<=bound)%nat -> SchemaEvaluationIndexBounds.classes bound entries.
Proof.
 induction entries as [|cls tail IH];cbn [classes_max];intro H;[constructor|].
 constructor;[apply class_bound;lia|apply IH;lia].
Qed.
Lemma initial_bounded native logical : NativeRepresentation.canonical_arena native (Protocol.formulas logical) ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical) (Protocol.classes logical) (initial_bound logical).
Proof.
 intro Harena. split.
 - apply SchemaEvaluationIndexBounds.canonical_formulas_raw;[exact Harena|]. apply formulas_bound. unfold initial_bound;apply Nat.le_max_l.
 - apply classes_bound. unfold initial_bound;apply Nat.le_max_r.
Qed.
(** Resolve the named schema, then check its finite schedule. Rejected names
    and arities need no evaluating arena budget. *)
Definition check native logical (ids:list nat) name :=
 match Protocol.lookup name (Protocol.bindings logical) with
 | Some (Protocol.schema_binding root)=>
   match Protocol.pf logical root with
   | Some cert=>if Nat.eqb (length ids) (Schemata.proof_arity cert) then
     Z.leb (Z.of_nat (SchemaMarking.size root)) maximum &&
     Z.ltb (Z.of_nat (length (Protocol.history logical))) maximum &&
     SchemaEvaluationIndexSchedule.check native root (length (Protocol.formulas logical)) (initial_bound logical) (length (Protocol.classes logical))
     else true
   | None=>true end
 | _=>true end.
Theorem resources native logical ids name :
 NativeRepresentation.canonical_arena native (Protocol.formulas logical) ->
 SchemaRepresentation.represents native logical -> check native logical ids name=true ->
 SchemaInstanceGeneralProtocol.resources native logical ids name.
Proof.
 intros Harena Hschemas Hcheck root cert actual Hlookup Hproof Hlength Hactual.
 unfold check in Hcheck. rewrite Hlookup,Hproof,Hlength,Nat.eqb_refl in Hcheck.
 rewrite !Bool.andb_true_iff in Hcheck. destruct Hcheck as [[Hgrid Hhistory] Hschedule].
 split;[now apply Z.leb_le|]. split;[now apply Z.ltb_lt|].
 apply (SchemaEvaluationIndexSchedule.resources native logical root actual (length (Protocol.formulas logical)) (initial_bound logical)).
 - exact (SchemaGraph.represented_ordered native logical Hschemas).
 - rewrite (SchemaMetadata.represents_length native _ (SchemaRepresentation.metadata native logical Hschemas)).
   pose proof (SchemaNodeMeaning.proof_lookup logical root cert Hproof) as Hroot. apply nth_error_Some;congruence.
 - reflexivity.
 - exact (initial_bounded native logical Harena).
 - exact Hschedule.
Qed.
Theorem command_resources native logical ids name :
 NativeRepresentation.canonical_arena native (Protocol.formulas logical) ->
 SchemaRepresentation.represents native logical -> check native logical ids name=true ->
 SchemaInstanceGeneralCommand.resources native logical ids name.
Proof. exact (resources native logical ids name). Qed.
End SchemaInstanceCheckedResources.
