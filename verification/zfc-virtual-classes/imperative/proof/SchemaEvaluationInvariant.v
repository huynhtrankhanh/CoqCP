From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash SchemaEvaluation SchemaGraph InternReserve.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationInvariant.
Import IndexExecution SipHashExecution.

Lemma meaning_extend fs classes extra_fs extra_classes rho depth expression id :
  SchemaEvaluation.meaning fs classes rho depth expression id ->
  SchemaEvaluation.meaning (fs++extra_fs) (classes++extra_classes) rho depth expression id.
Proof.
  destruct expression as [c|p|proof];cbn [SchemaEvaluation.meaning SchemaEvaluation.formula_value SchemaEvaluation.class_value].
  - intros [Hword Hlookup]. split;[exact Hword|]. eapply InternReserve.lookup_preserved;[exists extra_classes;reflexivity|exact Hlookup].
  - intros [Hword Hlookup]. split;[exact Hword|]. eapply InternReserve.lookup_preserved;[exists extra_fs;reflexivity|exact Hlookup].
  - intros [p [Hinfer [Hword Hlookup]]]. exists p. split;[exact Hinfer|]. split;[exact Hword|].
    eapply InternReserve.lookup_preserved;[exists extra_fs;reflexivity|exact Hlookup].
Qed.

Definition completed source root expressions rho fs classes native limit :=
  forall node depth expression,
    SchemaGraph.reachable source root node depth -> (SchemaGraph.key root node depth<limit)%nat ->
    nth_error expressions node=Some expression ->
    SchemaEvaluation.meaning fs classes rho depth expression
      (SchemaEvaluation.value native (SchemaGraph.key root node depth)).

Lemma completed_zero source root expressions rho fs classes native :
  completed source root expressions rho fs classes native 0.
Proof. intros node depth expression Hreach Hkey. lia. Qed.

Lemma completed_transport source root expressions rho fs classes s t limit extra_fs extra_classes :
  completed source root expressions rho fs classes s limit ->
  (forall key,(key<limit)%nat -> SchemaEvaluation.value t key=SchemaEvaluation.value s key) ->
  completed source root expressions rho (fs++extra_fs) (classes++extra_classes) t limit.
Proof.
  intros Hcompleted Hvalues node depth expression Hreach Hkey Hlookup.
  rewrite Hvalues by exact Hkey. apply meaning_extend. eapply Hcompleted;eassumption.
Qed.

Theorem completed_step source root expressions rho fs classes before after limit node depth expression :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  completed source root expressions rho fs classes before limit ->
  (forall key,(key<limit)%nat -> SchemaEvaluation.value after key=SchemaEvaluation.value before key) ->
  (depth<SchemaGraph.width root)%nat -> SchemaGraph.key root node depth=limit ->
  nth_error expressions node=Some expression ->
  SchemaEvaluation.meaning fs classes rho depth expression (SchemaEvaluation.value after limit) ->
  completed source root expressions rho fs classes after (S limit).
Proof.
  intros Hordered Hroot Hcompleted Hvalues Hdepth Hkey Hlookup Hmeaning other otherDepth otherExpression Hreachable Hbound Hother.
  destruct (Nat.lt_dec (SchemaGraph.key root other otherDepth) limit) as [Hprevious|Hcurrent].
  - rewrite Hvalues by exact Hprevious. eapply Hcompleted;eassumption.
  - assert (Hequal:SchemaGraph.key root other otherDepth=SchemaGraph.key root node depth) by lia.
    destruct (SchemaGraph.reachable_grid source root other otherDepth Hordered Hroot Hreachable) as [_ [HotherDepth _]].
    destruct (SchemaGraph.key_injective root other otherDepth node depth HotherDepth Hdepth Hequal) as [-> ->].
    rewrite Hlookup in Hother. injection Hother as <-. now rewrite Hkey.
Qed.

Theorem completed_skip source root expressions rho fs classes before after limit :
  completed source root expressions rho fs classes before limit ->
  (forall key,(key<limit)%nat -> SchemaEvaluation.value after key=SchemaEvaluation.value before key) ->
  (forall node depth,SchemaGraph.reachable source root node depth -> SchemaGraph.key root node depth<>limit) ->
  completed source root expressions rho fs classes after (S limit).
Proof.
  intros Hcompleted Hvalues Hskip node depth expression Hreachable Hbound Hlookup.
  assert (Hprevious:(SchemaGraph.key root node depth<limit)%nat) by (specialize (Hskip node depth Hreachable);lia).
  rewrite Hvalues by exact Hprevious. eapply Hcompleted;eassumption.
Qed.

Theorem completed_root source root expressions rho fs classes native expression :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  completed source root expressions rho fs classes native (SchemaGraph.width root*SchemaGraph.width root) ->
  nth_error expressions root=Some expression ->
  SchemaEvaluation.meaning fs classes rho 0 expression (SchemaEvaluation.value native (SchemaGraph.key root root 0)).
Proof.
  intros Hordered Hroot Hcompleted Hlookup. eapply Hcompleted;[constructor| |exact Hlookup].
  exact (proj2 (proj2 (SchemaGraph.reachable_grid source root root 0 Hordered Hroot (SchemaGraph.root_reachable source root)))).
Qed.

Theorem completed_proof source root expressions rho fs classes native cert :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
  completed source root expressions rho fs classes native (SchemaGraph.width root*SchemaGraph.width root) ->
  nth_error expressions root=Some (Protocol.PE cert) ->
  exists p,Schemata.infer rho 0 cert=Some p /\
    SchemaEvaluation.formula_value fs (SchemaEvaluation.value native (SchemaGraph.key root root 0)) p /\ SetTheory.derives p.
Proof.
  intros Hordered Hroot Hcompleted Hlookup.
  destruct (completed_root source root expressions rho fs classes native (Protocol.PE cert) Hordered Hroot Hcompleted Hlookup)
    as [p [Hinfer Hmeaning]]. exists p. split;[exact Hinfer|]. split;[exact Hmeaning|].
  exact (Guarantees.instance_sound rho 0 cert p Hinfer).
Qed.
End SchemaEvaluationInvariant.
