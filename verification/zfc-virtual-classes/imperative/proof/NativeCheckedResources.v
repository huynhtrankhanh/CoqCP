From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash NativeState NativeBasicDispatcher NativeFullDispatcher NativeGeneralDispatcher
 NativeAxiomTotal NativeProofSession AxiomTaggedInvariant SchemaEvaluationBoundedCell SchemaEvaluationIndexBudget
 SchemaEvaluationIndexBounds SchemaEvaluationIndexSetness SchemaInstanceCheckedResources
 ClassCertifyTotal ClassLookup FormulaTopology RenameMemoResourceBounds Representation ClassStorage.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeCheckedResources.
Import IndexExecution SipHashExecution.
Definition count logical := length(Protocol.formulas logical).
Definition bound logical := SchemaInstanceCheckedResources.initial_bound logical.
Definition common (native:Machine) logical request :=
 Z.leb (Z.of_nat(count logical)) 9223372036854775807 &&
 Z.ltb (Z.of_nat(length(Protocol.classes logical))) maximum &&
 Z.ltb (Z.of_nat(length(Protocol.history logical))) maximum &&
 Z.ltb (Z.of_nat(length(Protocol.bindings logical))) maximum &&
 Z.leb (Z.of_nat(length(memory native arraydef_0__names)+length(Protocol.object_name request))) maximum &&
 Z.ltb (Z.of_nat(length(Protocol.expressions logical))) maximum.
Definition binary logical :=
 Z.leb (Z.of_nat(count logical+2*(count logical*count logical)+13)) 9223372036854775807 &&
 Z.leb (Z.of_nat(5*(count logical*count logical)+1)) maximum &&
 Z.leb (2*Z.of_nat(bound logical)+3) maximum.
Definition axiom logical tag rawJ :=
 Z.leb (Z.of_nat(count logical+SchemaEvaluationIndexBudget.axiom_cost (count logical) tag)) 9223372036854775807 &&
 Z.leb (Z.of_nat(5*(count logical*count logical)+1)) maximum &&
 Z.leb (Z.of_nat(bound logical)+Z.of_nat rawJ+2) maximum.
Definition certify logical :=
 Z.leb (Z.of_nat(count logical+count logical*count logical+10)) 9223372036854775807 &&
 Z.leb (Z.of_nat(5*(count logical*count logical)+1)) maximum &&
 Z.leb (Z.of_nat(bound logical)+2) maximum.
Definition specific native logical request := match Protocol.opcode request,Protocol.arguments request with
 | 7%nat,[_;_] | 8%nat,[_;_]=>binary logical
 | 11%nat,[tag;_;rawJ;_]=>axiom logical tag rawJ
 | 14%nat,[_]=>certify logical
 | 24%nat,ids=>SchemaInstanceCheckedResources.check native logical ids (Protocol.object_name request)
 | _,_=>true end.
Definition check native logical request := common native logical request && specific native logical request.

Lemma common_resources native logical request : common native logical request=true ->
 NativeBasicDispatcher.resources native logical request /\ Z.of_nat(length(Protocol.expressions logical))<maximum.
Proof.
 unfold common. rewrite !Bool.andb_true_iff.
 intros [[[[[Hf Hc] Hh] Hb] Hn] He].
 apply Z.leb_le in Hf. apply Z.ltb_lt in Hc. apply Z.ltb_lt in Hh. apply Z.ltb_lt in Hb.
 apply Z.leb_le in Hn. apply Z.ltb_lt in He. split;[constructor;assumption|exact He].
Qed.
Lemma axiom_resources native logical tag a b c :
 NativeRepresentation.canonical_arena native (Protocol.formulas logical) ->
 FormulaTopology.ordered native(count logical) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 Z.of_nat a<=maximum -> axiom logical tag b=true -> NativeAxiomTotal.resources logical tag a b c.
Proof.
 intros Harena Htop Hfalse Ha Hcheck wanted Hconcrete.
 unfold axiom in Hcheck. rewrite !Bool.andb_true_iff in Hcheck.
 destruct Hcheck as [[Hroom Hfuel] Hindices]. apply Z.leb_le in Hroom,Hfuel,Hindices.
 pose proof(SchemaInstanceCheckedResources.initial_bounded native logical Harena) as [Hraw Hclasses].
 pose proof(NativeProofSession.ready_from_concrete logical tag a b c wanted Hconcrete) as Hready.
 assert(Hpositive:(0<count logical)%nat) by (unfold count;apply nth_error_Some;congruence).
 pose proof(SchemaEvaluationIndexBudget.axiom_ready native (Protocol.formulas logical) tag b (bound logical) (count logical) 0
  Harena Htop Hraw Hpositive ltac:(reflexivity) ltac:(intro;exact Hfuel) Hindices
  ltac:(unfold count,RenameMemoResourceBounds.doubling_limit in *;now rewrite Nat.add_0_r)) as Hdomain.
 destruct(Hdomain a (NativeProofSession.pick(Protocol.formulas logical)a) ltac:(unfold word;split;lia) ltac:(intro Hneeds;pose proof(proj1 Hready) as Hp;rewrite Hneeds in Hp;exact Hp))
  as [indexBound [Hrename Hbudget]].
 exists(NativeProofSession.pick(Protocol.formulas logical)a),(NativeProofSession.pick(Protocol.formulas logical)b),
  (NativeProofSession.pick(Protocol.formulas logical)c),indexBound.
 split;[exact Hready|]. split;[exact Hrename|]. now rewrite Nat.add_0_r in Hbudget.
Qed.

Theorem resources native logical request : Protocol.shape request -> NativeState.represents native logical ->
 FormulaTopology.ordered native(count logical) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> check native logical request=true -> NativeGeneralDispatcher.resources native logical request.
Proof.
 intros Hshape Hstate Htop Hfalse Hgood Hcheck. unfold check in Hcheck. apply Bool.andb_true_iff in Hcheck as [Hcommon Hspecific].
 destruct(common_resources _ _ _ Hcommon) as [Hbasic Hschema]. constructor;[exact Hbasic|exact Hschema|].
 pose proof(NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof(NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof(SchemaInstanceCheckedResources.initial_bounded native logical Harena) as [Hraw Hbounds].
 assert(Hpositive:(0<count logical)%nat) by (unfold count;apply nth_error_Some;congruence).
 destruct request as [opcode args name].
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 25%nat opcode.
 all:cbn [specific NativeGeneralDispatcher.specific_resources NativeFullDispatcher.specific_resources Protocol.opcode Protocol.arguments Protocol.object_name] in Hspecific|-*;try exact I.
 - destruct args as [|a [|b [|bad args]]];try exact I. cbn in Hspecific|-*.
   unfold binary in Hspecific. rewrite !Bool.andb_true_iff in Hspecific. destruct Hspecific as [[Hroom Hfuel] Hindices].
   apply Z.leb_le in Hroom,Hfuel,Hindices.
   pose proof(SchemaEvaluationIndexBudget.equal_ready native (Protocol.formulas logical) (Protocol.classes logical) (bound logical) (count logical) 0
    Harena Htop Hclasses Hgood Hraw Hbounds Hpositive ltac:(reflexivity) Hfuel ltac:(lia)
    ltac:(unfold count,RenameMemoResourceBounds.doubling_limit in *;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros ca cb Ha Hb. destruct(Hready a b ca cb Ha Hb) as [HreadyPair Hbudget].
   split;[exact HreadyPair|]. now rewrite Nat.add_0_r in Hbudget.
 - destruct args as [|a [|b [|bad args]]];try exact I. cbn in Hspecific|-*.
   unfold binary in Hspecific. rewrite !Bool.andb_true_iff in Hspecific. destruct Hspecific as [[Hroom Hfuel] Hindices].
   apply Z.leb_le in Hroom,Hfuel,Hindices.
   pose proof(SchemaEvaluationIndexBudget.member_ready native (Protocol.formulas logical) (Protocol.classes logical) (bound logical) (count logical) 0
    Harena Htop Hclasses Hgood Hraw Hbounds Hpositive ltac:(reflexivity) Hfuel Hindices
    ltac:(unfold count,RenameMemoResourceBounds.doubling_limit in *;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros ca cb Ha Hb. destruct(Hready a b ca cb Ha Hb) as [HreadyPair Hbudget].
   split;[exact HreadyPair|]. now rewrite Nat.add_0_r in Hbudget.
 - destruct args as [|tag [|a [|b [|c [|bad args]]]]];try exact I. cbn in Hspecific|-*.
   apply(axiom_resources native logical tag a b c Harena Htop Hfalse);[|exact Hspecific].
   destruct Hshape as [Hwords _]. inversion Hwords as [|tag' values Htag Hrest];subst tag' values.
   inversion Hrest as [|a' values Ha Htail];subst a' values. exact Ha.
 - destruct args as [|tid [|bad args]];try exact I. cbn in Hspecific|-*.
   unfold certify in Hspecific. rewrite !Bool.andb_true_iff in Hspecific. destruct Hspecific as [[Hroom Hfuel] Hindices].
   apply Z.leb_le in Hroom,Hfuel,Hindices.
   pose proof(SchemaEvaluationIndexSetness.uniform_ready native (Protocol.formulas logical) (Protocol.classes logical) (bound logical) (count logical) 0
    Harena Htop Hclasses Hgood Hfalse Hraw Hbounds ltac:(reflexivity) Hfuel Hindices
    ltac:(unfold count,RenameMemoResourceBounds.doubling_limit in *;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros cls flag c p Hlookup Hclass Hproof. exact(Hready cls c Hclass).
 - exact(SchemaInstanceCheckedResources.command_resources native logical args name Harena (NativeState.schema_representation _ _ Hstate) Hspecific).
Qed.
End NativeCheckedResources.
