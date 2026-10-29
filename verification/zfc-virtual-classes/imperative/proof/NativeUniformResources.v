From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash NativeState NativeBasicDispatcher NativeFullDispatcher NativeGeneralDispatcher
 NativeAxiomTotal NativeProofSession AxiomTaggedInvariant SchemaEvaluationBoundedCell SchemaEvaluationIndexBudget
 SchemaEvaluationIndexCell SchemaEvaluationIndexSetness SchemaUniformBudget NativeSchemaFieldBounds
 ClassLookup FormulaTopology RenameMemoResourceBounds Representation ClassStorage.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module NativeUniformResources.
Import IndexExecution SipHashExecution.
Definition guard arena index fuel := Z.leb(Z.of_nat arena)9223372036854775807 &&
 Z.leb(Z.of_nat(5*(fuel*fuel)+1))maximum && Z.leb(Z.of_nat index)maximum.
Definition check request F B C E N := match Protocol.opcode request,Protocol.arguments request with
 | 7%nat,[_;_]=>guard (F+2*(F*F)+6) (B+2) F
 | 8%nat,[_;_]=>guard (F+2*(F*F)+13) (2*B+3) F
 | 11%nat,[tag;_;_;_]=>guard (F+SchemaEvaluationIndexBudget.axiom_cost F tag) (B+N+2) F
 | 14%nat,[_]=>guard (F+F*F+10) (B+2) F
 | 24%nat,_=>guard (SchemaUniformBudget.formula_after F (SchemaUniformBudget.slots E))
    (SchemaUniformBudget.index_after E N B (SchemaUniformBudget.slots E))
    (SchemaUniformBudget.formula_after F (SchemaUniformBudget.slots E)) &&
    Z.leb(Z.of_nat(C+SchemaUniformBudget.slots E+1))maximum
 | _,_=>true end.
Lemma guard_values arena index fuel : guard arena index fuel=true ->
 Z.of_nat arena<=9223372036854775807 /\ Z.of_nat(5*(fuel*fuel)+1)<=maximum /\ Z.of_nat index<=maximum.
Proof.
 unfold guard. rewrite !Bool.andb_true_iff. intros [[Hf Hfuel] Hi].
 apply Z.leb_le in Hf,Hfuel,Hi. repeat split;assumption.
Qed.
Lemma axiom_resources native logical tag a b c F B N :
 NativeRepresentation.canonical_arena native(Protocol.formulas logical) ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)B ->
 (length(Protocol.formulas logical)<=F)%nat -> (b<=N)%nat -> Z.of_nat a<=maximum ->
 guard (F+SchemaEvaluationIndexBudget.axiom_cost F tag) (B+N+2) F=true -> NativeAxiomTotal.resources logical tag a b c.
Proof.
 intros Harena Htop Hfalse [Hraw Hclasses] HF Hb Ha Hcheck wanted Hconcrete.
 destruct(guard_values _ _ _ Hcheck) as [Hroom [Hfuel Hindices]].
 pose proof(NativeProofSession.ready_from_concrete logical tag a b c wanted Hconcrete) as Hready.
 assert(Hpositive:(0<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;congruence).
 pose proof(SchemaEvaluationIndexBudget.axiom_ready native(Protocol.formulas logical)tag b B F 0
  Harena Htop Hraw Hpositive HF ltac:(intro;exact Hfuel)
  ltac:(repeat rewrite Nat2Z.inj_add in Hindices;apply Nat2Z.inj_le in Hb;lia)
  ltac:(unfold RenameMemoResourceBounds.doubling_limit;repeat rewrite Nat2Z.inj_add in *;lia)) as Hdomain.
 destruct(Hdomain a (NativeProofSession.pick(Protocol.formulas logical)a) ltac:(unfold word;split;lia)
  ltac:(intro Hneeds;pose proof(proj1 Hready) as Hp;rewrite Hneeds in Hp;exact Hp)) as [bound [Hrename Hbudget]].
 exists(NativeProofSession.pick(Protocol.formulas logical)a),(NativeProofSession.pick(Protocol.formulas logical)b),
  (NativeProofSession.pick(Protocol.formulas logical)c),bound.
 split;[exact Hready|]. split;[exact Hrename|]. now rewrite Nat.add_0_r in Hbudget.
Qed.
Theorem resources native logical request F B C E N :
 Protocol.shape request -> NativeState.represents native logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> SchemaEvaluationIndexCell.bounded native(Protocol.formulas logical)(Protocol.classes logical)B ->
 (length(Protocol.formulas logical)<=F)%nat -> (length(Protocol.classes logical)<=C)%nat ->
 (length(Protocol.expressions logical)<=E)%nat -> NativeSchemaFieldBounds.fields native N ->
 Forall(fun value=>(value<=N)%nat)(Protocol.arguments request) ->
 NativeBasicDispatcher.resources native logical request -> Z.of_nat(length(Protocol.expressions logical))<maximum ->
 check request F B C E N=true -> NativeGeneralDispatcher.resources native logical request.
Proof.
 intros Hshape Hstate Htop Hfalse Hgood Hbounded HF HC HE Hfields Hargs Hbasic Hschema Hcheck.
 constructor;[exact Hbasic|exact Hschema|].
 pose proof(NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof(NativeState.class_representation _ _ Hstate) as Hclasses.
 destruct Hbounded as [Hraw Hbounds].
 assert(Hpositive:(0<length(Protocol.formulas logical))%nat) by (apply nth_error_Some;congruence).
 destruct request as [opcode args name].
 let rec cases count index := lazymatch count with O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 25%nat opcode.
 all:cbn [check NativeGeneralDispatcher.specific_resources NativeFullDispatcher.specific_resources Protocol.opcode Protocol.arguments Protocol.object_name] in Hcheck|-*;try exact I.
 - destruct args as [|a [|b [|bad args]]];try exact I. cbn in Hcheck|-*.
   destruct(guard_values _ _ _ Hcheck) as [Hroom [Hfuel Hindices]].
   pose proof(SchemaEvaluationIndexBudget.equal_ready native(Protocol.formulas logical)(Protocol.classes logical) B F 0
    Harena Htop Hclasses Hgood Hraw Hbounds Hpositive HF Hfuel
    ltac:(rewrite Nat2Z.inj_add in Hindices;exact Hindices)
    ltac:(unfold RenameMemoResourceBounds.doubling_limit;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros ca cb Ha Hb. destruct(Hready a b ca cb Ha Hb) as [Hpair Hbudget]. split;[exact Hpair|]. now rewrite Nat.add_0_r in Hbudget.
 - destruct args as [|a [|b [|bad args]]];try exact I. cbn in Hcheck|-*.
   destruct(guard_values _ _ _ Hcheck) as [Hroom [Hfuel Hindices]].
   pose proof(SchemaEvaluationIndexBudget.member_ready native(Protocol.formulas logical)(Protocol.classes logical) B F 0
    Harena Htop Hclasses Hgood Hraw Hbounds Hpositive HF Hfuel
    ltac:(repeat rewrite Nat2Z.inj_add in Hindices;lia)
    ltac:(unfold RenameMemoResourceBounds.doubling_limit;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros ca cb Ha Hb. destruct(Hready a b ca cb Ha Hb) as [Hpair Hbudget]. split;[exact Hpair|]. now rewrite Nat.add_0_r in Hbudget.
 - destruct args as [|tag [|a [|b [|c [|bad args]]]]];try exact I. cbn in Hcheck|-*.
   apply(axiom_resources native logical tag a b c F B N Harena Htop Hfalse (conj Hraw Hbounds) HF);try exact Hcheck.
   + cbn [Protocol.arguments] in Hargs. inversion Hargs as [|tag' tail Htag Hrest];subst tag' tail.
     inversion Hrest as [|a' tail Ha Hrest'];subst a' tail. inversion Hrest' as [|b' tail Hb Htail];subst b' tail. exact Hb.
   + destruct Hshape as [Hwords _]. inversion Hwords as [|tag' tail Htag Hrest];subst tag' tail.
     inversion Hrest as [|a' tail Ha Htail];subst a' tail. exact Ha.
 - destruct args as [|tid [|bad args]];try exact I. cbn in Hcheck|-*.
   destruct(guard_values _ _ _ Hcheck) as [Hroom [Hfuel Hindices]].
   pose proof(SchemaEvaluationIndexSetness.uniform_ready native(Protocol.formulas logical)(Protocol.classes logical)B F 0
    Harena Htop Hclasses Hgood Hfalse Hraw Hbounds HF Hfuel
    ltac:(rewrite Nat2Z.inj_add in Hindices;exact Hindices)
    ltac:(unfold RenameMemoResourceBounds.doubling_limit;repeat rewrite Nat2Z.inj_add in *;lia)) as Hready.
   intros cls flag c p Hlookup Hclass Hproof. exact(Hready cls c Hclass).
 - apply Bool.andb_true_iff in Hcheck as [Hguard Hclassroom].
   destruct(guard_values _ _ _ Hguard) as [Hformula [Hfuel Hindex]]. apply Z.leb_le in Hclassroom.
   exact(SchemaUniformBudget.protocol_resources native logical args name E N F B C
    (NativeState.schema_representation _ _ Hstate) HE (NativeSchemaFieldBounds.encoded_fields native N Hfields)
    HF HC (conj Hraw Hbounds) (NativeBasicDispatcher.history_room _ _ _ Hbasic) Hformula Hindex Hfuel Hclassroom).
Qed.
End NativeUniformResources.
