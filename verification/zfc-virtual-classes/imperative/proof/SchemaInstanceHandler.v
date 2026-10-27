From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl CommandChain CommandStructure
 ReplyNO AppendTheorem HistoryStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceHandler.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue R.
Definition suffix : LocalAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [CommandChain.handler_for CommandStructure.handler_24] in (CommandChain.handler_for funcdef_0__readNat 24) in
 multimatch code with context [bind (bind (numberLocalGet _ _ _ vardef_0__command_a) ?loopfun) ?after]=>
 let nested:=eval cbn beta in(loopfun 0%Z) in
 lazymatch nested with loop _ _=>exact (after tt) end end).
Local Opaque funcdef_0__no funcdef_0__schemaInstance funcdef_0__appendTheorem.
Lemma generated_fatal (f:Frame) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8<>0 ->
 execLocalObserved suffix (f,observations)=Some (tt,(f,observations)).
Proof.
 intros Hmeta Herror. unfold suffix.
 repeat first [progress cbn [optionBind fst snd negb bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
 rewrite bool_decide_false by exact Herror. reflexivity.
Qed.
Lemma generated_absent (f:Frame) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 nums f vardef_0__command_binding=maximum ->
 execLocalObserved suffix (f,observations)=Some (tt,(setMachine f (ReplyNOExecution.reply_state (machine f)),
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])).
Proof.
 intros Hmeta Herror Hbinding. unfold maximum in *. unfold suffix.
 repeat first [progress cbn [optionBind fst snd negb bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
  |progress rewrite Herror|progress rewrite Hbinding
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |multimatch goal with |-context[bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__no bs ns) state) in
   let Hsame:=fresh in assert (Hsame:expression=Some (tt,(ReplyNOExecution.reply_state (machine f),
    observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])))
    by apply ReplyNOExecution.generated_no;rewrite Hsame;clear Hsame end].
 reflexivity.
Qed.
Ltac suffix_primitives bound := repeat first [progress cbn [optionBind fst snd negb bind machine setMachine setNum nums]
 |NativePrimitives.primitive bound
 |progress rewrite RenameMemoControl.updated_same
 |progress rewrite RenameMemoControl.updated_other by discriminate
 |progress replace (Z.to_nat 8) with 8%nat by reflexivity
 |progress replace (Z.to_nat 18) with 18%nat by reflexivity
 |multimatch goal with |-context[bool_decide ?P]=>first
   [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
 |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bs ?ns) (?current,?trace)]=>
  let expression:=constr:(@execObserved I T EI R (funcdef_0__no bs ns) (current,trace)) in
  let Hsame:=fresh in assert (Hsame:expression=Some (tt,(ReplyNOExecution.reply_state current,
    trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}])))
    by apply ReplyNOExecution.generated_no;rewrite Hsame;clear Hsame end].
Lemma generated_wrong_kind (f:Frame) index offset size value flag kind observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 nums f vardef_0__command_binding=Z.of_nat index -> Z.of_nat index<maximum ->
 nth_error (memory (machine f) arraydef_0__bindings) index=Some (offset,size,value,flag,kind) -> kind<>2 ->
 execLocalObserved suffix (f,observations)=Some (tt,(setMachine f (ReplyNOExecution.reply_state (machine f)),
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])).
Proof.
 intros Hmeta Herror Hbinding Hindex Hraw Hkind. unfold maximum in *. unfold suffix.
 assert (Hbound:(index<length (memory (machine f) arraydef_0__bindings))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hraw) as Hnth.
 repeat first [progress rewrite Herror|progress rewrite Hbinding|progress rewrite Nat2Z.id
  |match goal with |-context[List.nth ?i ?xs ?zero]=>let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in assert (Hsame:expression=(offset,size,value,flag,kind)) by exact Hnth;rewrite Hsame;clear Hsame end
  |progress rewrite (bool_decide_false (Z.of_nat index=18446744073709551615)) by lia
  |suffix_primitives ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Hbinding,?Nat2Z.id;first[exact Hbound|lia])].
 reflexivity.
Qed.
Definition rooted (f:Frame) node := setNum f vardef_0__command_node (Z.of_nat node).
Lemma generated_bad_arity (f:Frame) index offset size node flag k a b c d ty arity count observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 nums f vardef_0__command_binding=Z.of_nat index -> Z.of_nat index<maximum ->
 nth_error (memory (machine f) arraydef_0__bindings) index=Some (offset,size,Z.of_nat node,flag,2) ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (k,a,b,c,d,ty,Z.of_nat arity) ->
 nums f vardef_0__command_a=Z.of_nat count ->
 (count<>arity \/ meta_value (machine f) 18=0) ->
 execLocalObserved suffix (f,observations)=Some (tt,(setMachine (rooted f node) (ReplyNOExecution.reply_state (machine f)),
 observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])).
Proof.
 intros Hmeta Herror Hbinding Hindex Hraw Hnode Hcount Hbad. unfold maximum in *. unfold suffix.
 assert (Hbound:(index<length (memory (machine f) arraydef_0__bindings))%nat) by (apply nth_error_Some;congruence).
 assert (Hnodebound:(node<length (memory (machine f) arraydef_0__schemaNodes))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hraw) as Hnth.
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0,0,0) Hnode) as HnodeNth.
 destruct Hbad as [Hbad|Hbad].
 2: destruct (Nat.eq_dec count arity) as [Hequal|Hdifferent];[subst count|].
 all: repeat first [progress rewrite Herror|progress rewrite Hbinding|progress rewrite Hcount|progress rewrite Nat2Z.id
  |match goal with |-context[List.nth ?i ?xs ?zero]=>let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in first
     [assert (Hsame:expression=(offset,size,Z.of_nat node,flag,2)) by exact Hnth
     |assert (Hsame:expression=(k,a,b,c,d,ty,Z.of_nat arity)) by exact HnodeNth];rewrite Hsame;clear Hsame end
  |progress rewrite Hbad
  |progress rewrite (bool_decide_false (Z.of_nat index=18446744073709551615)) by lia
  |multimatch goal with |-context[bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by (cbn [fst snd];lia)|progress rewrite (bool_decide_false P) by (cbn [fst snd];lia)] end
  |suffix_primitives ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Hbinding,?Nat2Z.id;first[exact Hbound|exact Hnodebound|lia])].
 all: unfold rooted;reflexivity.
Qed.
Definition instance_arguments root : varsfuncdef_0__schemaInstance->Z := update (fun _=>0) vardef_0__schemaInstance_root root.
Definition evaluation : LocalAction unit := ltac:(
 let code:=eval unfold suffix in suffix in
 multimatch code with context [bind (bind (numberLocalGet _ _ _ vardef_0__command_node) ?call) ?after]=>
 let called:=eval cbv beta iota zeta delta [bind] in(call 0%Z) in
 lazymatch called with liftToWithLocalVariables (funcdef_0__schemaInstance _ _)=>exact (bind (bind (numberLocalGet _ _ _ vardef_0__command_node) call) after) end end).
Definition after_evaluation : LocalAction unit := ltac:(
 let code:=eval unfold evaluation in evaluation in
 lazymatch code with bind _ ?after=>exact (after tt) end).
Lemma evaluation_parts : evaluation=((numberLocalGet _ _ _ vardef_0__command_node >>=
 fun root=>liftToWithLocalVariables (funcdef_0__schemaInstance (fun _=>false) (instance_arguments root))) >>=fun _=>after_evaluation).
Proof. reflexivity. Qed.
Lemma option_unit {S} (response:option (unit*S)) :
 optionBind response (fun value=>Some (tt,snd value))=response.
Proof. destruct response as [[[] state]|];reflexivity. Qed.
Lemma generated_checked (f:Frame) index offset size node flag k a b c d ty arity observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
 nums f vardef_0__command_binding=Z.of_nat index -> Z.of_nat index<maximum ->
 nth_error (memory (machine f) arraydef_0__bindings) index=Some (offset,size,Z.of_nat node,flag,2) ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (k,a,b,c,d,ty,Z.of_nat arity) ->
 nums f vardef_0__command_a=Z.of_nat arity -> meta_value (machine f) 18<>0 ->
 execLocalObserved suffix (f,observations)=execLocalObserved evaluation (rooted f node,observations).
Proof.
 intros Hmeta Herror Hbinding Hindex Hraw Hnode Hcount Hvalid. unfold maximum in *. unfold suffix.
 assert (Hbound:(index<length (memory (machine f) arraydef_0__bindings))%nat) by (apply nth_error_Some;congruence).
 assert (Hnodebound:(node<length (memory (machine f) arraydef_0__schemaNodes))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0) Hraw) as Hnth.
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0,0,0) Hnode) as HnodeNth.
 repeat first [progress rewrite Herror|progress rewrite Hbinding|progress rewrite Hcount|progress rewrite Nat2Z.id
  |match goal with |-context[List.nth ?i ?xs ?zero]=>let expression:=constr:(List.nth i xs zero) in
    let Hsame:=fresh in first
     [assert (Hsame:expression=(offset,size,Z.of_nat node,flag,2)) by exact Hnth
     |assert (Hsame:expression=(k,a,b,c,d,ty,Z.of_nat arity)) by exact HnodeNth];rewrite Hsame;clear Hsame end
  |progress rewrite (bool_decide_false (Z.of_nat index=18446744073709551615)) by lia
  |suffix_primitives ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Hbinding,?Nat2Z.id;first[exact Hbound|exact Hnodebound|lia])].
 unfold evaluation,rooted.
 repeat first [progress rewrite local_bind
  |progress cbn [optionBind fst snd execLocalObserved machine setMachine setNum nums]
  |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
  |progress rewrite RenameMemoControl.updated_same
  |progress rewrite RenameMemoControl.updated_other by discriminate
  |progress rewrite option_unit].
 reflexivity.
Qed.
Lemma generated_evaluation (f:Frame) root built observations :
 nums f vardef_0__command_node=Z.of_nat root ->
 execObserved (funcdef_0__schemaInstance (fun _=>false) (instance_arguments (Z.of_nat root))) (machine f,observations)=Some (tt,(built,observations)) ->
 execLocalObserved evaluation (f,observations)=execLocalObserved after_evaluation (setMachine f built,observations).
Proof.
 intros Hroot Hrun. rewrite evaluation_parts,local_bind.
 repeat first [progress cbn [optionBind fst snd]
  |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
  |progress rewrite Hroot
  |match goal with |-context[@execObserved ?I ?T ?EI ?R (funcdef_0__schemaInstance ?bs ?ns) ?state]=>
   let expression:=constr:(@execObserved I T EI R (funcdef_0__schemaInstance bs ns) state) in
   let Hsame:=fresh in assert(Hsame:expression=Some(tt,(built,observations))) by exact Hrun;rewrite Hsame;clear Hsame end].
 reflexivity.
Qed.
End SchemaInstanceHandler.
