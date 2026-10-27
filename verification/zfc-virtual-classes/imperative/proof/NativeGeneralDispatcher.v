From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeBasicDispatcher NativeFullDispatcher NativeCommandBoundary
 NativeSchemaGeneralBoundary SchemaInstanceGeneralCommand SchemaInstanceCommand FormulaTopology ClassLookup.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralDispatcher.
Import IndexExecution SipHashExecution.
Definition specific_resources native logical request :=
 if Nat.eqb (Protocol.opcode request) 24 then
   SchemaInstanceGeneralCommand.resources native logical (Protocol.arguments request) (Protocol.object_name request)
 else NativeFullDispatcher.specific_resources native logical request.
Record resources native logical request : Prop := Resources {
 basic_resources : NativeBasicDispatcher.resources native logical request;
 schema_room : Z.of_nat(length (Protocol.expressions logical))<maximum;
 command_resources : specific_resources native logical request
}.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length (memory native arraydef_0__meta))%nat -> (0<length (memory native arraydef_0__sipState))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat -> (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first (Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> ClassLookup.wellformed native ->
 NoDup (map fst (Protocol.bindings logical)) -> resources native logical request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 NativeBasicDispatcher.checked native logical request bs ns tail observations.
Proof.
 intros Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique
   [Hbasic Hschema Hspecific] Hinput.
 destruct (Nat.eq_dec (Protocol.opcode request) 24%nat) as [Hinstance|Hother].
 - destruct request as [opcode ids name]. cbn [Protocol.opcode] in Hinstance. subst opcode.
   destruct Hshape as [Hwords Hfields]. cbn [Protocol.arguments Protocol.object_name] in Hwords,Hfields.
   destruct Hfields as [Hname Hlength].
   change (meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.instance_rest in Hinput.
   change (SchemaInstanceGeneralCommand.resources native logical ids name) in Hspecific.
   destruct (NativeSchemaGeneralBoundary.generated_canonical native bs ns logical ids name tail observations
     Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hspecific)
     as (final & reply & next & Hrun & Hstep & Hnext & Hclear & HsafeNext & Hio).
   eapply NativeBasicDispatcher.finish;eassumption.
 - assert (Hfull:NativeFullDispatcher.resources native logical request).
   { constructor;try assumption. unfold specific_resources in Hspecific.
     rewrite (proj2 (Nat.eqb_neq _ _) Hother) in Hspecific. exact Hspecific. }
   exact (NativeFullDispatcher.generated_canonical native logical request bs ns tail observations
     Hshape Hbound Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hfull Hinput).
Qed.
End NativeGeneralDispatcher.
