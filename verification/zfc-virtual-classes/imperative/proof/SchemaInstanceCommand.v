From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal RenameMemoControl CommandInput CommandDispatch CommandChain
 SchemaInstanceHandler SchemaInstancePrefix SchemaInstanceArguments SchemaInstanceProtocol NativeState NameRepresentation Representation ClassStorage HistoryRefinement
 ReadNat ReadToken TokenByte TokenFrame ArenaFrame FormulaProjection ClassLookup FormulaTopology HashTable SchemaRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SchemaInstanceHandler.Frame.
Definition LocalAction := SchemaInstanceHandler.LocalAction.
Section Numbers.
Context (watched:varsfuncdef_0__command).
Definition number_safe (effect:WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) :=
 match effect with NumberLocalSet _ _ _ name _=>name<>watched|_=>True end.
Fixpoint number_ro {R} (code:LocalAction R) : Prop := match code with
 |Done _ _ _ _=>True|Dispatch _ _ _ effect cont=>number_safe effect /\ forall response,number_ro (cont response) end.
Lemma number_bind {A B} (code:LocalAction A) (next:A->LocalAction B) :
 number_ro code -> (forall value,number_ro (next value)) -> number_ro (code>>=next).
Proof. induction code as [value|effect cont IH];[intros _ H;apply H|]. intros [Hsafe Hcode] Hnext. split;[exact Hsafe|]. intro;apply IH;auto. Qed.
Lemma number_lift {R} (code:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
 number_ro (liftToWithLocalVariables code).
Proof. induction code;cbn [liftToWithLocalVariables Action_rect number_ro number_safe];auto. Qed.
Lemma number_step effect (f:Frame) observations value final after :
 number_safe effect -> localStepObserved effect (f,observations)=Some (value,(final,after)) -> nums final watched=nums f watched.
Proof.
 intros Hsafe Hrun. destruct effect as [effect|name|name value'|name|name value'];unfold localStepObserved in Hrun;cbn [fst snd] in Hrun.
 - destruct (observedStep effect (machine f,observations)) as [[response [middle trace]]|];[|discriminate].
   cbn [optionBind fst snd] in Hrun. injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. reflexivity.
 - injection Hrun as _ <- <-. cbn [nums setNum]. apply RenameMemoControl.updated_other. now cbn [number_safe] in Hsafe.
Qed.
Lemma number_preserves {R} (code:LocalAction R) (f:Frame) observations value final after :
 number_ro code -> execLocalObserved code (f,observations)=Some (value,(final,after)) -> nums final watched=nums f watched.
Proof.
 induction code as [result|effect cont IH] in f,observations|-*.
 - intros _ Hrun. injection Hrun as _ <- <-. reflexivity.
 - intros [Hsafe Hcode] Hrun. cbn [execLocalObserved] in Hrun.
   destruct (localStepObserved effect (f,observations)) as [[response [middle trace]]|] eqn:Hstep;[|discriminate].
   cbn [optionBind fst snd] in Hrun. rewrite (IH response middle trace (Hcode response) Hrun).
   eapply number_step;eassumption.
Qed.
End Numbers.
Ltac number_frames := first
 [lazymatch goal with |- number_ro _ (Done _ _ _ _)=>exact I end
 |lazymatch goal with |- number_ro _ (bind _ _)=>apply number_bind;[number_frames|intro;number_frames] end
 |apply number_lift
 |lazymatch goal with |- number_ro _ (if ?test then _ else _)=>destruct test;number_frames end
 |lazymatch goal with |- number_ro _ (Dispatch _ _ _ _ _)=>split;[cbn [number_safe];intuition congruence|intro;number_frames] end
 |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet retrieve store grow trap readChar writeChar flush shortCircuitAnd shortCircuitOr addInt subInt multInt];number_frames].
Local Opaque funcdef_0__no funcdef_0__schemaInstance funcdef_0__appendTheorem.
Lemma suffix_opcode_readonly : number_ro vardef_0__command_op SchemaInstanceHandler.suffix.
Proof. unfold SchemaInstanceHandler.suffix. number_frames. Qed.

Theorem handler_opcode (f final:Frame) logical name ids observations trace :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (1024<=length (memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 ->
 NameRepresentation.represents (machine f) (Protocol.bindings logical) ->
 Protocol.valid_name name ->
 Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 forall tail,
 stdin (machine f)=name++32::(decimalBytes (length ids)++SchemaInstanceArguments.separator_for ids::(SchemaInstanceArguments.wire ids++tail)) ->
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat 24) (f,observations)=Some (tt,(final,trace)) ->
 nums final vardef_0__command_op=nums f vardef_0__command_op.
Proof.
 intros Hmeta Htoken Hpending Herror Hnames Hname Hwords Hlength tail Hinput Hrun.
 destruct (SchemaInstancePrefix.generated_canonical f (Protocol.bindings logical) name ids tail SchemaInstanceHandler.suffix observations
   Hmeta Htoken Hpending Herror Hnames Hname Hwords Hlength Hinput)
 as (looked & Hframe & Houtcome & Hprefix & Hrest).
 rewrite SchemaInstancePrefix.actual_handler in Hrun.
 assert (Hsuffix:execLocalObserved SchemaInstanceHandler.suffix
  (SchemaInstancePrefix.finished f looked ids tail,observations)=Some (tt,(final,trace))).
 { transitivity (execLocalObserved (SchemaInstancePrefix.with_suffix SchemaInstanceHandler.suffix) (f,observations));[symmetry;exact Hprefix|exact Hrun]. }
 rewrite (number_preserves vardef_0__command_op SchemaInstanceHandler.suffix
   (SchemaInstancePrefix.finished f looked ids tail) observations tt final trace suffix_opcode_readonly Hsuffix).
 apply SchemaInstancePrefix.finished_number;discriminate.
Qed.

Definition payload ids name tail := name++32::(decimalBytes (length ids)++SchemaInstanceArguments.separator_for ids::(SchemaInstanceArguments.wire ids++tail)).
Definition opcode_state s ids name tail := CommandInput.parsed s 50 [52] (payload ids name tail).
Definition initial_frame s bs ns ids name tail :=
 CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} (opcode_state s ids name tail) 24.
Lemma parsed_token_length s ch chars tail :
 length (memory (CommandInput.parsed s ch chars tail) arraydef_0__token)=length (memory s arraydef_0__token).
Proof. unfold CommandInput.parsed,ReadNatExecution.token_number. rewrite store_meta_other by discriminate.
 apply ReadTokenExecution.pending_token_length. Qed.
Lemma parsed_pending s ch chars tail : (17<length (memory s arraydef_0__meta))%nat ->
 meta_value (CommandInput.parsed s ch chars tail) 15=0.
Proof.
 intro Hmeta. unfold CommandInput.parsed,ReadNatExecution.token_number,ReadTokenExecution.pending_result.
 rewrite !meta_store_other by discriminate.
 change (meta_value (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.started s ch) 1 chars) 17 1) 15=0).
 rewrite meta_store_other by discriminate. rewrite ReadTokenExecution.put_many_meta_other by discriminate.
 unfold ReadTokenExecution.started. apply meta_store_same.
 rewrite ReadTokenExecution.put_meta_length,ReadTokenExecution.reset_length. lia.
Qed.
Lemma parsed_state s ch chars tail logical : NativeState.represents s logical ->
 NativeState.represents (CommandInput.parsed s ch chars tail) logical.
Proof.
 intros Hstate. destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas]. constructor.
 - exact (ArenaFrame.storage_arena _ _ _ (CommandInput.parsed_storage s ch chars tail) Harena).
 - unfold ClassStorage.represents. rewrite CommandInput.parsed_meta_other by lia.
   rewrite CommandInput.parsed_other by discriminate. exact Hclasses.
 - unfold HistoryRefinement.represents. rewrite CommandInput.parsed_meta_other by lia.
   rewrite CommandInput.parsed_other by discriminate. exact Hhistory.
 - unfold NameRepresentation.represents. rewrite !CommandInput.parsed_meta_other by lia.
   rewrite !CommandInput.parsed_other by discriminate. exact Hnames.
 - eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
   + apply CommandInput.parsed_meta_other;lia.
   + apply CommandInput.parsed_other;discriminate.
Qed.
Lemma canonical_wire ids name tail :
 50::52::32::payload ids name tail=Protocol.request_bytes (Protocol.Req 24 ids name)++tail.
Proof.
 rewrite SchemaInstanceArguments.request_wire. unfold payload. change
 (([50;52]++32::name++32::decimalBytes (length ids)++SchemaInstanceArguments.separator_for ids::(SchemaInstanceArguments.wire ids++tail))=
 ([50;52]++32::name++32::decimalBytes (length ids)++match ids with []=>[10]|_=>32::SchemaInstanceArguments.wire ids end)++tail).
 destruct ids;cbn [SchemaInstanceArguments.separator_for SchemaInstanceArguments.wire];repeat first [progress rewrite <-app_assoc|progress cbn [List.app]];reflexivity.
Qed.

(** Pure capacity conditions for the states reached while parsing the request. *)
Definition resources s bs ns logical ids name tail :=
 SchemaInstanceProtocol.handler_resources (initial_frame s bs ns ids name tail) logical ids name tail.

(** The command is entered after tapeEnd has consumed its first byte, 50 ('2').
    Pending slot 15 holds byte+1; the unread bytes start with 52 ('4'). *)
Theorem generated_canonical s bs ns logical ids name tail observations :
 (31<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (0<length (memory s arraydef_0__sipState))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=51 -> meta_value s 8=0 ->
 Protocol.valid_name name -> Forall (fun id=>Z.of_nat id<=maximum) ids -> Z.of_nat (length ids)<=maximum ->
 stdin s=52::32::payload ids name tail ->
 NativeState.represents s logical -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 Guarantees.safe logical -> resources s bs ns logical ids name tail ->
 exists final reply next,
 execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 24 ids name) reply next /\
 NativeState.represents final next /\ meta_value final 8=0 /\ Guarantees.safe next.
Proof.
 intros Hmeta Htoken Hsip Hprint Hpending Herror Hname Hwords Hlength Hinput Hstate Hgood Htop Hfalse Hsafe Hresources.
 set (op:=opcode_state s ids name tail).
 set (f:=initial_frame s bs ns ids name tail).
 assert (HopMeta:(31<length (memory op arraydef_0__meta))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_meta_length. }
 assert (HopToken:(1024<=length (memory op arraydef_0__token))%nat).
 { unfold op,opcode_state. now rewrite parsed_token_length. }
 assert (HopSip:(0<length (memory op arraydef_0__sipState))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopPrint:(20<=length (memory op arraydef_0__printBuffer))%nat).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopError:meta_value op 8=0).
 { unfold op,opcode_state. now rewrite CommandInput.parsed_meta_other by lia. }
 assert (HopPending:meta_value op 15=0).
 { unfold op,opcode_state. apply parsed_pending;lia. }
 assert (HopRead:execObserved (funcdef_0__readNat (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(op,observations))).
 { unfold op,opcode_state. apply (CommandInput.generated_pending s (fun _=>false) (fun _=>0) 24 50 [52] 32 (payload ids name tail) observations);
   try assumption;try reflexivity;try (unfold maximum;lia);try lia.
   unfold TokenByteExecution.separator;left;reflexivity. }
 assert (HopNumber:meta_value op 11=24).
 { unfold op,opcode_state. exact (CommandInput.parsed_number s 24 50 [52] (payload ids name tail) ltac:(lia) ltac:(unfold maximum;lia) eq_refl). }
 assert (HopValid:meta_value op 14=1).
 { unfold op,opcode_state. apply CommandInput.parsed_valid;lia. }
 assert (HopState:NativeState.represents op logical).
 { unfold op,opcode_state. exact (parsed_state s 50 [52] (payload ids name tail) logical Hstate). }
 assert (HopGood:ClassLookup.wellformed op).
 { eapply ClassLookup.transport;[|exact Hgood]. unfold op,opcode_state. apply CommandInput.parsed_other;discriminate. }
 assert (HopTop:FormulaTopology.ordered op (length (Protocol.formulas logical))).
 { apply (FormulaTopology.same s);[exact Htop|]. intros parent Hparent.
   unfold HashTableInvariant.tuple_at,op,opcode_state. now rewrite CommandInput.parsed_other by discriminate. }
 assert (HopInput:stdin op=payload ids name tail) by reflexivity.
 destruct HopState as [HopArena HopClasses HopHistory HopNames HopSchemas].
 destruct (SchemaInstanceProtocol.generated_handler f logical ids name tail observations
   HopMeta HopToken HopSip HopPrint HopPending HopError Hname Hwords Hlength HopInput
   HopArena HopClasses HopHistory HopNames HopSchemas HopGood HopTop Hfalse Hsafe Hresources)
 as (after & reply & next & Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hclear & HnextSafe).
 assert (HopFinal:nums after vardef_0__command_op=24).
 { change (nums after vardef_0__command_op=nums f vardef_0__command_op).
   exact (handler_opcode f after logical name ids observations _ ltac:(change (18<length (memory op arraydef_0__meta))%nat;lia) HopToken HopPending HopError HopNames Hname Hwords Hlength tail HopInput Hrun). }
 assert (HfinalMeta:(8<length (memory (machine after) arraydef_0__meta))%nat).
 { pose proof (proj1 (proj1 (proj1 Harena))) as Hbound. lia. }
 assert (Hcommand:execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(machine after,
   observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}]))).
 { pose proof (CommandDispatch.generated_positive_command s bs ns after op 24 observations
    (observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes reply;unreadInput:=tail|}])
    HopRead ltac:(lia) HopNumber HopValid HopError ltac:(lia) HopFinal Hrun HfinalMeta Hclear) as Hdispatch.
   unfold f,initial_frame,CommandDispatch.opcode_frame,op,opcode_state in Hdispatch.
   cbn [machine setNum setMachine] in Hdispatch. now rewrite CommandInput.parsed_output in Hdispatch. }
 exists (machine after),reply,next. split;[exact Hcommand|]. split;[exact Hstep|]. split.
 - constructor;assumption.
 - split;assumption.
Qed.
End SchemaInstanceCommand.


