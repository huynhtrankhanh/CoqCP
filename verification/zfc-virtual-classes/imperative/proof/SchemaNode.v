From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives InternTail
  RenameMemoControl SchemaMetadata SchemaRepresentation SchemaCheck ReplyOK ReplyNO FormulaProjection Representation FormulaTopology HashTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaNode.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode) withLocalVariablesReturnValue R.
Definition raw_node := (Z*Z*Z*Z*Z*Z*Z)%type.
Definition grown (s : Machine) n := withMemory s
  (growArrays (memory s) arraydef_0__schemaNodes (S n) (0,0,0,0,0,0,0)).
Definition written s n (raw : raw_node) := withMemory (grown s n)
  (modifyArray (memory (grown s n)) arraydef_0__schemaNodes n raw).
Definition result s n raw := store_meta (ReplyOKExecution.reply_state (written s n raw) n) 16 (Z.of_nat (S n)).
Lemma grown_other s n name : name<>arraydef_0__schemaNodes -> memory (grown s n) name=memory s name.
Proof. intro Hname. unfold grown. cbn [withMemory memory]. now rewrite growArrays_other. Qed.
Lemma written_other s n raw name : name<>arraydef_0__schemaNodes -> memory (written s n raw) name=memory s name.
Proof. intro Hname. unfold written. cbn [withMemory memory]. rewrite InternTailExecution.modify_other by exact Hname. now apply grown_other. Qed.
Lemma grown_meta s n i : meta_value (grown s n) i=meta_value s i.
Proof. unfold meta_value. now rewrite grown_other by discriminate. Qed.
Lemma written_meta s n raw i : meta_value (written s n raw) i=meta_value s i.
Proof. unfold meta_value. now rewrite written_other by discriminate. Qed.
Lemma written_nodes s n raw : memory (written s n raw) arraydef_0__schemaNodes=
  <[n:=raw]>(growList (memory s arraydef_0__schemaNodes) (S n) (0,0,0,0,0,0,0)).
Proof. unfold written,grown. cbn [withMemory memory]. now rewrite InternTailExecution.modify_same,growArrays_same. Qed.
Lemma written_app s n raw : length (memory s arraydef_0__schemaNodes)=n ->
  memory (written s n raw) arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes++[raw].
Proof.
  intro Hlength. rewrite written_nodes. rewrite <-Hlength. unfold growList.
  replace (S (length (memory s arraydef_0__schemaNodes))-length (memory s arraydef_0__schemaNodes))%nat with 1%nat by lia.
  cbn [repeat]. clear Hlength n. induction (memory s arraydef_0__schemaNodes) as [|x xs IH]; [reflexivity|]. cbn. f_equal. exact IH.
Qed.
Lemma result_other s n raw name : name<>arraydef_0__meta -> name<>arraydef_0__schemaNodes -> name<>arraydef_0__printBuffer ->
  memory (result s n raw) name=memory s name.
Proof. intros Hm Hn Hp. unfold result. rewrite store_meta_other by exact Hm. rewrite ReplyOKExecution.reply_other by exact Hp. now apply written_other. Qed.
Lemma result_meta_length s n raw : length (memory (result s n raw) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. rewrite store_meta_length,ReplyOKExecution.reply_other,written_other by discriminate. reflexivity. Qed.
Lemma result_meta_other s n raw slot : slot<>16%nat -> meta_value (result s n raw) slot=meta_value s slot.
Proof. intro Hslot. unfold result. rewrite meta_store_other by exact Hslot. unfold meta_value. now rewrite ReplyOKExecution.reply_other,written_other by discriminate. Qed.
Lemma result_count s n raw : (16<length (memory s arraydef_0__meta))%nat -> meta_value (result s n raw) 16=Z.of_nat (S n).
Proof. intro Hmeta. unfold result. apply meta_store_same. rewrite ReplyOKExecution.reply_other,written_other by discriminate. exact Hmeta. Qed.
Lemma result_nodes s n raw : length (memory s arraydef_0__schemaNodes)=n ->
  memory (result s n raw) arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes++[raw].
Proof. intro Hlength. unfold result. rewrite store_meta_other,ReplyOKExecution.reply_other by discriminate. now apply written_app. Qed.
Lemma result_output s n raw : stdout (result s n raw)=stdout s++Protocol.reply_bytes (Protocol.OK n).
Proof. unfold result. change (stdout (ReplyOKExecution.reply_state (written s n raw) n)=stdout s++Protocol.reply_bytes (Protocol.OK n)). rewrite ReplyOKExecution.reply_output. reflexivity. Qed.
Lemma result_input s n raw : stdin (result s n raw)=stdin s.
Proof. unfold result. change (stdin (ReplyOKExecution.reply_state (written s n raw) n)=stdin s). rewrite ReplyOKExecution.reply_input. reflexivity. Qed.
Lemma result_projection s n raw : FormulaProjection.storage s (result s n raw).
Proof.
  split; [apply result_meta_length|]. split.
  - intros name Hneeded. unfold FormulaProjection.needed in Hneeded.
    destruct Hneeded as [-> | [-> | [-> | ->]]]; apply result_other; discriminate.
  - repeat split; apply result_meta_other; lia.
Qed.
Lemma reply_meta s n i : meta_value (ReplyOKExecution.reply_state s n) i=meta_value s i.
Proof. unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
Definition finish : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__schemaNode_body in funcdef_0__schemaNode_body in
  let rec skip n code := lazymatch n with O => exact code | S ?rest =>
    lazymatch code with bind ?head ?next => let tail := eval cbv beta in (next tt) in skip rest tail end end in
  skip 13%nat code).
Definition row (f : Frame) : raw_node :=
  (nums f vardef_0__schemaNode_kind,nums f vardef_0__schemaNode_a,nums f vardef_0__schemaNode_b,
   nums f vardef_0__schemaNode_c,nums f vardef_0__schemaNode_d,nums f vardef_0__schemaNode_type,meta_value (machine f) 19).
Local Opaque Imperative.update funcdef_0__ok funcdef_0__no.
Theorem generated_finish (f : Frame) n observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 16=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved finish (f,observations)=Some (tt,(setMachine f (result (machine f) n (row f)),
    observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin (machine f)|}])).
Proof.
  intros Hmeta Hvalid Hcount Hword Hbuffer.
  assert (Hnext:coerceInt (Z.of_nat n+1) 64=Z.of_nat (S n)).
  { rewrite coerce_word by (unfold word;lia). lia. }
  unfold maximum in Hword. destruct f as [s bs ns]. cbn [machine] in *.
  unfold finish.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress unfold addInt at 1
    |NativePrimitives.primitive ltac:(fun frame name slot=> cbn [machine setMachine];
       repeat first [rewrite store_meta_length|rewrite ReplyOKExecution.reply_other by discriminate|rewrite grown_other by discriminate|rewrite written_other by discriminate
         |progress unfold grown|progress cbn [withMemory memory]
         |rewrite growArrays_other by discriminate|rewrite InternTailExecution.modify_other by discriminate
         |rewrite growArrays_same|rewrite growList_length|rewrite Nat2Z.id]; lia)
    |progress fold (grown s n)
    |progress change (withMemory (grown s n) (modifyArray (memory (grown s n)) arraydef_0__schemaNodes n
       (ns vardef_0__schemaNode_kind,ns vardef_0__schemaNode_a,ns vardef_0__schemaNode_b,ns vardef_0__schemaNode_c,
        ns vardef_0__schemaNode_d,ns vardef_0__schemaNode_type,meta_value s 19))) with (written s n (row {|machine:=s;bools:=bs;nums:=ns|}))
    |progress rewrite Hcount|progress rewrite Hnext|progress rewrite Nat2Z.id
    |progress rewrite reply_meta|progress rewrite grown_meta|progress rewrite written_meta
    |progress rewrite meta_store_other by lia
    |progress replace (Z.to_nat 16) with 16%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 16) with 16%nat by reflexivity
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 19) with 19%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
    |match goal with |- context [execObserved (funcdef_0__ok ?pbs ?pns) (?source,?trace)] =>
      rewrite (ReplyOKExecution.generated_ok source pbs pns n trace ltac:(cbn [Imperative.update];reflexivity) ltac:(unfold maximum;lia)
        ltac:(rewrite written_other by discriminate;exact Hbuffer)) end
    |progress rewrite ReplyOKExecution.reply_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.

Definition parts : list (LocalAction unit) := ltac:(
  let code := eval unfold funcdef_0__schemaNode_body in funcdef_0__schemaNode_body in
  let rec take n code := lazymatch n with O => constr:(@nil (LocalAction unit)) | S ?rest =>
    lazymatch code with bind ?head ?next =>
      let tail := eval cbv beta in (next tt) in let suffix := take rest tail in
      constr:(head::suffix) end end in
  let code := take 13%nat code in exact code).
Fixpoint prepend (parts : list (LocalAction unit)) (rest : LocalAction unit) : LocalAction unit :=
  match parts with []=>rest | head::tail=>head >>= fun _=>prepend tail rest end.
Definition prefix : LocalAction unit := prepend parts (Done _ _ _ tt).
Lemma actual_body : funcdef_0__schemaNode_body=prepend parts finish.
Proof. reflexivity. Qed.
Lemma prepend_exec steps rest f observations :
  execLocalObserved (prepend steps rest) (f,observations)=
  optionBind (execLocalObserved (prepend steps (Done _ _ _ tt)) (f,observations))
    (fun response=>execLocalObserved rest (snd response)).
Proof.
  induction steps as [|head tail IH] in f,observations |- *; [reflexivity|].
  cbn [prepend]. rewrite !local_bind.
  destruct (execLocalObserved head (f,observations)) as [[value [middle trace]]|] eqn:Hhead; [|reflexivity].
  destruct value. cbn [optionBind fst snd]. apply IH.
Qed.
Definition initialized s := store_meta (store_meta s 18 1) 19 0.
Definition variable_state s variable := store_meta (initialized s) 19 (Z.of_nat (S variable)).
Ltac validation_steps Hmeta := repeat first [progress cbn [optionBind fst snd negb]
  |progress rewrite Nat2Z.id
  |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
    repeat rewrite store_meta_length; repeat rewrite store_meta_other by discriminate; rewrite ?Nat2Z.id; lia)
  |progress replace (Z.to_nat 1) with 1%nat by reflexivity
  |progress replace (Z.to_nat 2) with 2%nat by reflexivity
  |progress replace (Z.to_nat 3) with 3%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 16) with 16%nat by reflexivity
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |progress replace (Z.to_nat 19) with 19%nat by reflexivity
  |progress rewrite meta_store_other by lia
  |progress rewrite meta_store_same by (repeat rewrite store_meta_length;lia)
  |progress rewrite RenameMemoControl.updated_same
  |progress rewrite RenameMemoControl.updated_other by discriminate
  |match goal with |- context [bool_decide ?P] => first
    [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
].
Theorem generated_variable_prefix (f : Frame) variable observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__schemaNode_kind=0 -> nums f vardef_0__schemaNode_a=Z.of_nat variable ->
  Z.of_nat (S variable)<=maximum ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (setNum f vardef_0__schemaNode_type 0) (variable_state (machine f) variable),observations)).
Proof.
  intros Hmeta Hkind Ha Hword.
  assert (Hnext:coerceInt (Z.of_nat variable+1) 64=Z.of_nat (S variable)).
  { rewrite coerce_word by (unfold word;lia). lia. }
  unfold maximum in Hword. destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold prefix,parts. cbn [prepend]. repeat first [progress validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha|progress unfold addInt at 1|progress rewrite Hnext].
  reflexivity.
Qed.
Theorem generated_variable s bs ns variable n observations :
  (19<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaNode_kind=0 -> ns vardef_0__schemaNode_a=Z.of_nat variable ->
  Z.of_nat (S variable)<=maximum -> meta_value s 16=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  let raw:=(0,Z.of_nat variable,ns vardef_0__schemaNode_b,ns vardef_0__schemaNode_c,ns vardef_0__schemaNode_d,0,Z.of_nat (S variable)) in
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    result (variable_state s variable) n raw,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin s|}])).
Proof.
  intros Hmeta Hkind Ha Hvar Hcount Hword Hbuffer raw.
  unfold funcdef_0__schemaNode. rewrite eliminate_correct,actual_body,prepend_exec.
  fold prefix.
  pose proof (generated_variable_prefix {|machine:=s;bools:=bs;nums:=ns|} variable observations Hmeta Hkind Ha Hvar) as Hprefix.
  unfold Frame in Hprefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish _ n observations).
  - cbn [optionBind fst snd]. unfold row,raw. cbn [setMachine machine setNum nums bools].
    rewrite RenameMemoControl.updated_same,!RenameMemoControl.updated_other by discriminate.
    rewrite Hkind,Ha. unfold variable_state. rewrite meta_store_same by (unfold initialized;rewrite !store_meta_length;lia).
    reflexivity.
  - cbn [machine setMachine]. unfold variable_state,initialized. rewrite !store_meta_length. exact Hmeta.
  - cbn [machine setMachine]. unfold variable_state,initialized. rewrite meta_store_other by lia.
    rewrite meta_store_other by lia. rewrite meta_store_same by lia. lia.
  - cbn [machine setMachine]. unfold variable_state,initialized. rewrite !meta_store_other by lia. exact Hcount.
  - exact Hword.
  - cbn [machine setMachine]. unfold variable_state,initialized. rewrite !store_meta_other by discriminate. exact Hbuffer.
Qed.

Theorem generated_finish_rejected (f : Frame) observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 18=0 ->
  execLocalObserved finish (f,observations)=Some (tt,(setMachine f (ReplyNOExecution.reply_state (machine f)),
    observations++[{|flushedOutput:=stdout (machine f)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine f)|}])).
Proof.
  intros Hmeta Hvalid. destruct f as [s bs ns]. cbn [machine] in *.
  unfold finish. repeat first [progress validation_steps Hmeta|progress rewrite Hvalid
    |progress rewrite ReplyNOExecution.generated_no]. reflexivity.
Qed.
Theorem generated_finish_overflow (f : Frame) observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 16=maximum ->
  execLocalObserved finish (f,observations)=Some (tt,(setMachine f (store_meta (machine f) 8 1),observations)).
Proof.
  intros Hmeta Hvalid Hfull. unfold maximum in Hfull. destruct f as [s bs ns]. cbn [machine] in *.
  unfold finish. repeat first [progress validation_steps Hmeta|progress rewrite Hfull]. reflexivity.
Qed.
Definition typed_frame (f : Frame) typ :=
  if bool_decide (typ=0) then setNum f vardef_0__schemaNode_type 0
  else setNum (setNum f vardef_0__schemaNode_type 0) vardef_0__schemaNode_type typ.
Lemma typed_frame_value f typ : nums (typed_frame f typ) vardef_0__schemaNode_type=typ.
Proof.
  unfold typed_frame. destruct (bool_decide (typ=0)) eqn:Htyp.
  - apply bool_decide_eq_true in Htyp. subst typ. cbn [nums setNum]. apply RenameMemoControl.updated_same.
  - cbn [nums setNum]. apply RenameMemoControl.updated_same.
Qed.
Lemma typed_frame_other f typ name : name<>vardef_0__schemaNode_type -> nums (typed_frame f typ) name=nums f name.
Proof.
  intro Hname. unfold typed_frame. destruct (bool_decide (typ=0)); cbn [nums setNum];
    now repeat rewrite RenameMemoControl.updated_other by exact Hname.
Qed.
Lemma typed_frame_machine f typ : machine (typed_frame f typ)=machine f.
Proof. unfold typed_frame. destruct (bool_decide (typ=0));reflexivity. Qed.
Lemma typed_frame_bools f typ : bools (typed_frame f typ)=bools f.
Proof. unfold typed_frame. destruct (bool_decide (typ=0));reflexivity. Qed.
Lemma row_typed f typ state : row (setMachine (typed_frame f typ) state)=
  (nums f vardef_0__schemaNode_kind,nums f vardef_0__schemaNode_a,nums f vardef_0__schemaNode_b,
   nums f vardef_0__schemaNode_c,nums f vardef_0__schemaNode_d,typ,meta_value state 19).
Proof.
  unfold row. change ((nums (typed_frame f typ) vardef_0__schemaNode_kind,
    nums (typed_frame f typ) vardef_0__schemaNode_a,nums (typed_frame f typ) vardef_0__schemaNode_b,
    nums (typed_frame f typ) vardef_0__schemaNode_c,nums (typed_frame f typ) vardef_0__schemaNode_d,
    nums (typed_frame f typ) vardef_0__schemaNode_type,meta_value state 19)=
    (nums f vardef_0__schemaNode_kind,nums f vardef_0__schemaNode_a,nums f vardef_0__schemaNode_b,
     nums f vardef_0__schemaNode_c,nums f vardef_0__schemaNode_d,typ,meta_value state 19)).
  rewrite typed_frame_value,!typed_frame_other by discriminate. reflexivity.
Qed.
Theorem generated_literal_prefix (f : Frame) kind index typ observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__schemaNode_kind=kind -> nums f vardef_0__schemaNode_a=Z.of_nat index ->
  ((kind=1 /\ typ=0 /\ Z.of_nat index<meta_value (machine f) 2) \/
   (kind=2 /\ typ=1 /\ Z.of_nat index<meta_value (machine f) 1)) ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (typed_frame f typ) (initialized (machine f)),observations)).
Proof.
  intros Hmeta Hkind Ha [[-> [-> Hbound]]|[-> [-> Hbound]]];
    destruct f as [s bs ns]; cbn [machine nums] in *;
    unfold typed_frame; cbn [bool_decide]; unfold prefix,parts; cbn [prepend];
    repeat first [progress validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha];reflexivity.
Qed.
Theorem generated_literal s bs ns kind index typ n observations :
  (19<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaNode_kind=kind -> ns vardef_0__schemaNode_a=Z.of_nat index ->
  ((kind=1 /\ typ=0 /\ Z.of_nat index<meta_value s 2) \/
   (kind=2 /\ typ=1 /\ Z.of_nat index<meta_value s 1)) ->
  meta_value s 16=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  let raw:=(kind,Z.of_nat index,ns vardef_0__schemaNode_b,ns vardef_0__schemaNode_c,ns vardef_0__schemaNode_d,typ,0) in
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    result (initialized s) n raw,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin s|}])).
Proof.
  intros Hmeta Hkind Ha Hvalid Hcount Hword Hbuffer raw.
  unfold funcdef_0__schemaNode. rewrite eliminate_correct,actual_body,prepend_exec. fold prefix.
  pose proof (generated_literal_prefix {|machine:=s;bools:=bs;nums:=ns|} kind index typ observations Hmeta Hkind Ha Hvalid) as Hprefix.
  unfold Frame in Hprefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish _ n observations).
  - rewrite row_typed. cbn [optionBind fst snd]. unfold raw. cbn [nums].
    rewrite Hkind,Ha. unfold initialized. rewrite meta_store_same by (cbn [machine]; rewrite store_meta_length;lia). reflexivity.
  - cbn [machine setMachine]. unfold initialized. rewrite !store_meta_length. exact Hmeta.
  - cbn [machine setMachine]. unfold initialized. rewrite meta_store_other by lia. rewrite meta_store_same by lia. lia.
  - cbn [machine setMachine]. unfold initialized. rewrite !meta_store_other by lia. exact Hcount.
  - exact Hword.
  - cbn [machine setMachine]. unfold initialized. rewrite !store_meta_other by discriminate. exact Hbuffer.
Qed.
Theorem generated_saved_prefix (f : Frame) tid fid observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__schemaNode_kind=11 -> nums f vardef_0__schemaNode_a=Z.of_nat tid ->
  Z.of_nat tid<meta_value (machine f) 3 ->
  nth_error (memory (machine f) arraydef_0__theorems) tid=Some (Z.of_nat fid) ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (setNum (setNum (setNum f vardef_0__schemaNode_type 0) vardef_0__schemaNode_type 2) vardef_0__schemaNode_a (Z.of_nat fid)) (initialized (machine f)),observations)).
Proof.
  intros Hmeta Hkind Ha Hcount Hraw.
  assert (Hbound:(tid<length (memory (machine f) arraydef_0__theorems))%nat) by (apply nth_error_Some;congruence).
  pose proof (List.nth_error_nth _ _ 0 Hraw) as Hnth.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold prefix,parts. cbn [prepend].
  repeat first [progress validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha
    |progress rewrite store_meta_other by discriminate|progress rewrite Hnth]. match goal with |- context [@List.nth ?A ?i ?xs ?zero] =>
    let expression:=constr:(@List.nth A i xs zero) in
    let Hsame:=fresh in assert (Hsame:expression=Z.of_nat fid) by exact Hnth;
    rewrite Hsame end. reflexivity.
Qed.
Theorem generated_saved s bs ns tid fid n observations :
  (19<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaNode_kind=11 -> ns vardef_0__schemaNode_a=Z.of_nat tid ->
  Z.of_nat tid<meta_value s 3 -> nth_error (memory s arraydef_0__theorems) tid=Some (Z.of_nat fid) ->
  meta_value s 16=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  let raw:=(11,Z.of_nat fid,ns vardef_0__schemaNode_b,ns vardef_0__schemaNode_c,ns vardef_0__schemaNode_d,2,0) in
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    result (initialized s) n raw,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin s|}])).
Proof.
  intros Hmeta Hkind Ha Htid Hraw Hcount Hword Hbuffer raw.
  unfold funcdef_0__schemaNode. rewrite eliminate_correct,actual_body,prepend_exec. fold prefix.
  pose proof (generated_saved_prefix {|machine:=s;bools:=bs;nums:=ns|} tid fid observations Hmeta Hkind Ha Htid Hraw) as Hprefix.
  unfold Frame in Hprefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish _ n observations).
  - cbn [optionBind fst snd]. unfold row,raw. cbn [setMachine machine setNum nums bools].
    repeat rewrite RenameMemoControl.updated_other by discriminate.
    rewrite !RenameMemoControl.updated_same. rewrite Hkind.
    unfold initialized. rewrite meta_store_same by (cbn [machine]; rewrite store_meta_length;lia). reflexivity.
  - cbn [machine setMachine]. unfold initialized. rewrite !store_meta_length. exact Hmeta.
  - cbn [machine setMachine]. unfold initialized. rewrite meta_store_other by lia. rewrite meta_store_same by lia. lia.
  - cbn [machine setMachine]. unfold initialized. rewrite !meta_store_other by lia. exact Hcount.
  - exact Hword.
  - cbn [machine setMachine]. unfold initialized. rewrite !store_meta_other by discriminate. exact Hbuffer.
Qed.

Lemma initialized_length s : length (memory (initialized s) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold initialized. now rewrite !store_meta_length. Qed.
Lemma initialized_represents s expressions : SchemaMetadata.represents s expressions ->
  SchemaMetadata.represents (initialized s) expressions.
Proof.
  intro Hrep. apply (SchemaMetadata.transport s); [| |exact Hrep].
  - unfold initialized. now rewrite !meta_store_other by lia.
  - unfold initialized. now rewrite !store_meta_other by discriminate.
Qed.
Lemma semantic_length s expressions index expected :
  length (memory (SchemaCheck.semantic_result s expressions index expected) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. exact (proj1 (SchemaCheck.semantic_storage s expressions index expected)). Qed.
Definition check_many expressions (requests : list (nat*Z)) s :=
  fold_left (fun state request => SchemaCheck.semantic_result state expressions (fst request) (snd request)) requests s.
Definition reference_requests kind a b c d : list (nat*Z) :=
  match kind with
  | 3%nat => [(a,1)]
  | 4%nat | 5%nat => [(a,0);(b,0)]
  | 6%nat => [(a,1);(b,1)]
  | 7%nat => [(a,1)]
  | 8%nat =>
    (if bool_decide (a=0%nat \/ a=1%nat \/ a=2%nat \/ a=3%nat \/ a=4%nat \/ a=15%nat \/ a=16%nat) then [(b,1)] else [])++
    (if bool_decide (a=0%nat \/ a=1%nat \/ a=4%nat) then [(c,1)] else [])++
    (if bool_decide (a=1%nat) then [(d,1)] else [])
  | 9%nat => [(a,2);(b,2)]
  | 10%nat => [(a,2)]
  | _ => []
  end.
Definition reference_type kind : Z := if bool_decide (kind=3%nat) then 0 else if bool_decide (kind<8)%nat then 1 else 2.
Definition reference_initial s kind a :=
  if bool_decide (kind=8%nat /\ (17<a)%nat) then SchemaCheck.rejected (initialized s) else initialized s.
Definition reference_state s expressions kind a b c d :=
  check_many expressions (reference_requests kind a b c d) (reference_initial s kind a).
Ltac schema_state_meta :=
  repeat first [rewrite semantic_length|rewrite initialized_length|rewrite store_meta_length|progress unfold SchemaCheck.rejected]; assumption.
Ltac schema_state_rep :=
  repeat first [apply SchemaCheck.preserves_schema|apply initialized_represents]; assumption.
Ltac schema_reference_call expressions Hmeta Hrep :=
  match goal with |- context [execObserved (funcdef_0__schemaCheck ?bs ?ns) (?source,?trace)] =>
    lazymatch ns with
    | Imperative.update (Imperative.update ?base vardef_0__schemaCheck_node (Z.of_nat ?i)) vardef_0__schemaCheck_type ?expected =>
      rewrite (SchemaCheck.generated_total source bs ns expressions i expected trace
        ltac:(schema_state_meta) ltac:(schema_state_rep)
        ltac:(rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same)
        ltac:(apply RenameMemoControl.updated_same))
    end
  end.
Lemma semantic_meta_other s expressions index expected slot : slot<>18%nat -> slot<>19%nat ->
  meta_value (SchemaCheck.semantic_result s expressions index expected) slot=meta_value s slot.
Proof.
  intros H18 H19. unfold SchemaCheck.semantic_result,SchemaCheck.checked,SchemaCheck.typed,SchemaCheck.rejected.
  destruct (nth_error expressions index) as [expression|];
    try destruct (bool_decide (meta_value s 19<Z.of_nat (SchemaMetadata.arity expression)));
    try destruct (bool_decide (SchemaMetadata.kind expression<>expected));
    repeat rewrite meta_store_other by assumption; reflexivity.
Qed.
Lemma semantic_other s expressions index expected name : name<>arraydef_0__meta ->
  memory (SchemaCheck.semantic_result s expressions index expected) name=memory s name.
Proof.
  intro Hname. unfold SchemaCheck.semantic_result,SchemaCheck.checked,SchemaCheck.typed,SchemaCheck.rejected.
  destruct (nth_error expressions index) as [expression|];
    try destruct (bool_decide (meta_value s 19<Z.of_nat (SchemaMetadata.arity expression)));
    try destruct (bool_decide (SchemaMetadata.kind expression<>expected));
    repeat rewrite store_meta_other by exact Hname; reflexivity.
Qed.
Lemma semantic_input s expressions index expected : stdin (SchemaCheck.semantic_result s expressions index expected)=stdin s.
Proof.
  unfold SchemaCheck.semantic_result,SchemaCheck.checked,SchemaCheck.typed,SchemaCheck.rejected.
  destruct (nth_error expressions index) as [expression|];
    try destruct (bool_decide (meta_value s 19<Z.of_nat (SchemaMetadata.arity expression)));
    try destruct (bool_decide (SchemaMetadata.kind expression<>expected)); reflexivity.
Qed.
Lemma semantic_output s expressions index expected : stdout (SchemaCheck.semantic_result s expressions index expected)=stdout s.
Proof.
  unfold SchemaCheck.semantic_result,SchemaCheck.checked,SchemaCheck.typed,SchemaCheck.rejected.
  destruct (nth_error expressions index) as [expression|];
    try destruct (bool_decide (meta_value s 19<Z.of_nat (SchemaMetadata.arity expression)));
    try destruct (bool_decide (SchemaMetadata.kind expression<>expected)); reflexivity.
Qed.
Lemma check_many_length expressions requests s : length (memory (check_many expressions requests s) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof.
  induction requests as [|[index expected] tail IH] in s|-*; [reflexivity|].
  unfold check_many in *. cbn [fold_left fst snd]. rewrite IH. apply semantic_length.
Qed.
Lemma check_many_meta_other expressions requests s slot : slot<>18%nat -> slot<>19%nat ->
  meta_value (check_many expressions requests s) slot=meta_value s slot.
Proof.
  intros H18 H19. induction requests as [|[index expected] tail IH] in s|-*; [reflexivity|].
  unfold check_many in *. cbn [fold_left fst snd]. rewrite IH. exact (semantic_meta_other s expressions index expected slot H18 H19).
Qed.
Lemma check_many_other expressions requests s name : name<>arraydef_0__meta ->
  memory (check_many expressions requests s) name=memory s name.
Proof.
  intro Hname. induction requests as [|[index expected] tail IH] in s|-*; [reflexivity|].
  unfold check_many in *. cbn [fold_left fst snd]. rewrite IH. exact (semantic_other s expressions index expected name Hname).
Qed.
Lemma check_many_input expressions requests s : stdin (check_many expressions requests s)=stdin s.
Proof.
  induction requests as [|[index expected] tail IH] in s|-*; [reflexivity|].
  unfold check_many in *. cbn [fold_left fst snd]. rewrite IH. apply semantic_input.
Qed.
Lemma check_many_output expressions requests s : stdout (check_many expressions requests s)=stdout s.
Proof.
  induction requests as [|[index expected] tail IH] in s|-*; [reflexivity|].
  unfold check_many in *. cbn [fold_left fst snd]. rewrite IH. apply semantic_output.
Qed.
Lemma reference_length s expressions kind a b c d :
  length (memory (reference_state s expressions kind a b c d) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold reference_state,reference_initial,SchemaCheck.rejected. rewrite check_many_length.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)); rewrite ?store_meta_length,initialized_length; reflexivity. Qed.
Lemma reference_meta_other s expressions kind a b c d slot : slot<>18%nat -> slot<>19%nat ->
  meta_value (reference_state s expressions kind a b c d) slot=meta_value s slot.
Proof.
  intros H18 H19. unfold reference_state. rewrite check_many_meta_other by assumption.
  unfold reference_initial,SchemaCheck.rejected,initialized.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)); repeat rewrite meta_store_other by assumption; reflexivity.
Qed.
Lemma reference_other s expressions kind a b c d name : name<>arraydef_0__meta ->
  memory (reference_state s expressions kind a b c d) name=memory s name.
Proof.
  intro Hname. unfold reference_state. rewrite check_many_other by exact Hname.
  unfold reference_initial,SchemaCheck.rejected,initialized.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)); repeat rewrite store_meta_other by exact Hname; reflexivity.
Qed.
Lemma reference_input s expressions kind a b c d : stdin (reference_state s expressions kind a b c d)=stdin s.
Proof. unfold reference_state. rewrite check_many_input. unfold reference_initial,SchemaCheck.rejected,initialized.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)); reflexivity. Qed.
Lemma reference_output s expressions kind a b c d : stdout (reference_state s expressions kind a b c d)=stdout s.
Proof. unfold reference_state. rewrite check_many_output. unfold reference_initial,SchemaCheck.rejected,initialized.
  destruct (bool_decide (kind=8%nat /\ (17<a)%nat)); reflexivity. Qed.
Definition valid_reference expressions (request : nat*Z) :=
  exists expression, nth_error expressions (fst request)=Some expression /\ SchemaMetadata.kind expression=snd request.
Definition reference_width expressions (request : nat*Z) :=
  match nth_error expressions (fst request) with Some expression=>Z.of_nat (SchemaMetadata.arity expression)|None=>0 end.
Lemma check_many_valid expressions requests s :
  (19<length (memory s arraydef_0__meta))%nat ->
  Forall (valid_reference expressions) requests -> meta_value s 18=1 ->
  meta_value (check_many expressions requests s) 18=1 /\
  meta_value (check_many expressions requests s) 19=
    fold_left (fun width request=>Z.max width (reference_width expressions request)) requests (meta_value s 19).
Proof.
  induction requests as [|[index expected] tail IH] in s|-*.
  - intros Hmeta Hvalid Hflag. split;[exact Hflag|reflexivity].
  - intros Hmeta Hvalid Hflag. inversion Hvalid as [|request rest Hrequest Htail];subst request rest.
    destruct Hrequest as [expression [Hlookup Hkind]]. cbn [fst snd] in Hlookup,Hkind.
    assert (Hnextmeta:(19<length (memory (SchemaCheck.semantic_result s expressions index expected) arraydef_0__meta))%nat).
    { rewrite semantic_length. exact Hmeta. }
    assert (Hnextflag:meta_value (SchemaCheck.semantic_result s expressions index expected) 18=1).
    { rewrite SchemaCheck.semantic_flag by exact Hmeta. rewrite Hlookup,Hkind.
      rewrite bool_decide_false by congruence. exact Hflag. }
    destruct (IH _ Hnextmeta Htail Hnextflag) as [Hdone Hwidth].
    split.
    + exact Hdone.
    + unfold check_many. cbn [fold_left fst snd]. unfold check_many in Hwidth. rewrite Hwidth.
      rewrite SchemaCheck.semantic_width by exact Hmeta. rewrite Hlookup.
      unfold reference_width. cbn [fst snd]. rewrite Hlookup. reflexivity.
Qed.
Theorem generated_reference_prefix (f : Frame) expressions kind a b c d observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  SchemaMetadata.represents (machine f) expressions ->
  nums f vardef_0__schemaNode_kind=Z.of_nat kind ->
  nums f vardef_0__schemaNode_a=Z.of_nat a -> nums f vardef_0__schemaNode_b=Z.of_nat b ->
  nums f vardef_0__schemaNode_c=Z.of_nat c -> nums f vardef_0__schemaNode_d=Z.of_nat d ->
  (3<=kind<=7)%nat \/ (9<=kind<=10)%nat ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (typed_frame f (reference_type kind)) (reference_state (machine f) expressions kind a b c d),observations)).
Proof.
  intros Hmeta Hrep Hkind Ha Hb Hc Hd Hrange.
  assert (Hcases:kind=3%nat \/ kind=4%nat \/ kind=5%nat \/ kind=6%nat \/ kind=7%nat \/ kind=9%nat \/ kind=10%nat) by lia.
  destruct Hcases as [Hcase | [Hcase | [Hcase | [Hcase | [Hcase | [Hcase | Hcase]]]]]]; subst kind;
    destruct f as [s bs ns]; cbn [machine nums] in *;
    unfold prefix,parts; cbn [prepend];
    unfold reference_state,reference_initial,reference_requests,reference_type,typed_frame,check_many;
    cbn [fold_left bool_decide fst snd];
    repeat first [progress validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha|progress rewrite Hb
      |progress rewrite Hc|progress rewrite Hd|progress fold (initialized s)
      |schema_reference_call expressions Hmeta Hrep]; reflexivity.
Qed.

Theorem generated_axiom_prefix (f : Frame) expressions a b c d observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  SchemaMetadata.represents (machine f) expressions ->
  nums f vardef_0__schemaNode_kind=8 ->
  nums f vardef_0__schemaNode_a=Z.of_nat a -> nums f vardef_0__schemaNode_b=Z.of_nat b ->
  nums f vardef_0__schemaNode_c=Z.of_nat c -> nums f vardef_0__schemaNode_d=Z.of_nat d ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (typed_frame f 2) (reference_state (machine f) expressions 8 a b c d),observations)).
Proof.
  intros Hmeta Hrep Hkind Ha Hb Hc Hd.
  let rec cases depth tag := lazymatch depth with
    O => idtac
  | S ?rest => let next:=fresh "tag" in destruct tag as [|next]; [idtac|cases rest next]
  end in cases 18%nat a.
  all: destruct f as [s bs ns]; cbn [machine nums] in *;
    unfold prefix,parts; cbn [prepend];
    unfold reference_state,reference_initial,reference_requests,typed_frame,check_many;
    cbn [fold_left bool_decide fst snd];
    repeat first [progress validation_steps Hmeta|progress rewrite Hkind|progress rewrite Ha|progress rewrite Hb
      |progress rewrite Hc|progress rewrite Hd|progress fold (initialized s)
      |schema_reference_call expressions Hmeta Hrep]; reflexivity.
Qed.
Theorem generated_reference_prefix_total (f : Frame) expressions kind a b c d observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  SchemaMetadata.represents (machine f) expressions ->
  nums f vardef_0__schemaNode_kind=Z.of_nat kind ->
  nums f vardef_0__schemaNode_a=Z.of_nat a -> nums f vardef_0__schemaNode_b=Z.of_nat b ->
  nums f vardef_0__schemaNode_c=Z.of_nat c -> nums f vardef_0__schemaNode_d=Z.of_nat d ->
  (3<=kind<=10)%nat ->
  execLocalObserved prefix (f,observations)=Some (tt,(
    setMachine (typed_frame f (reference_type kind)) (reference_state (machine f) expressions kind a b c d),observations)).
Proof.
  intros Hmeta Hrep Hkind Ha Hb Hc Hd Hrange.
  destruct (Nat.eq_dec kind 8) as [Hcase|Hcase].
  - subst kind. exact (generated_axiom_prefix f expressions a b c d observations Hmeta Hrep Hkind Ha Hb Hc Hd).
  - apply generated_reference_prefix; [exact Hmeta|exact Hrep|exact Hkind|exact Ha|exact Hb|exact Hc|exact Hd|lia].
Qed.
Theorem generated_after_prefix s bs ns (validated : Frame) n observations :
  execLocalObserved prefix ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (tt,(validated,observations)) ->
  (19<length (memory (machine validated) arraydef_0__meta))%nat ->
  meta_value (machine validated) 18<>0 -> meta_value (machine validated) 16=Z.of_nat n ->
  Z.of_nat n<maximum -> (20<=length (memory (machine validated) arraydef_0__printBuffer))%nat ->
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    result (machine validated) n (row validated),observations++[{|flushedOutput:=stdout (machine validated)++Protocol.reply_bytes (Protocol.OK n);
       unreadInput:=stdin (machine validated)|}])).
Proof.
  intros Hprefix Hmeta Hvalid Hcount Hword Hbuffer.
  unfold funcdef_0__schemaNode. rewrite eliminate_correct,actual_body,prepend_exec. fold prefix.
  rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish validated n observations Hmeta Hvalid Hcount Hword Hbuffer). reflexivity.
Qed.
Theorem generated_reference s bs ns expressions kind a b c d n observations :
  (19<length (memory s arraydef_0__meta))%nat -> SchemaMetadata.represents s expressions ->
  ns vardef_0__schemaNode_kind=Z.of_nat kind ->
  ns vardef_0__schemaNode_a=Z.of_nat a -> ns vardef_0__schemaNode_b=Z.of_nat b ->
  ns vardef_0__schemaNode_c=Z.of_nat c -> ns vardef_0__schemaNode_d=Z.of_nat d ->
  (3<=kind<=10)%nat ->
  meta_value (reference_state s expressions kind a b c d) 18<>0 ->
  meta_value s 16=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory s arraydef_0__printBuffer))%nat ->
  let validated:=reference_state s expressions kind a b c d in
  let raw:=(Z.of_nat kind,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,reference_type kind,meta_value validated 19) in
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    result validated n raw,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin s|}])).
Proof.
  intros Hmeta Hrep Hkind Ha Hb Hc Hd Hrange Hvalid Hcount Hword Hbuffer validated raw.
  unfold funcdef_0__schemaNode. rewrite eliminate_correct,actual_body,prepend_exec. fold prefix.
  pose proof (generated_reference_prefix_total {|machine:=s;bools:=bs;nums:=ns|} expressions kind a b c d observations
    Hmeta Hrep Hkind Ha Hb Hc Hd Hrange) as Hprefix.
  unfold Frame in Hprefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish _ n observations).
  - rewrite row_typed. cbn [optionBind fst snd nums]. rewrite Hkind,Ha,Hb,Hc,Hd.
    rewrite reference_output,reference_input. reflexivity.
  - cbn [machine setMachine]. rewrite reference_length. exact Hmeta.
  - exact Hvalid.
  - cbn [machine setMachine]. rewrite reference_meta_other by lia. exact Hcount.
  - exact Hword.
  - cbn [machine setMachine]. rewrite reference_other by discriminate. exact Hbuffer.
Qed.
Lemma reference_represents s logical kind a b c d : SchemaRepresentation.represents s logical ->
  SchemaRepresentation.represents (reference_state s (Protocol.expressions logical) kind a b c d) logical.
Proof.
  intro Hrep. apply (SchemaRepresentation.transport s _ logical logical Hrep).
  - apply reference_meta_other;lia.
  - apply reference_other;discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Lemma reference_projection s expressions kind a b c d : FormulaProjection.storage s (reference_state s expressions kind a b c d).
Proof.
  split;[apply reference_length|]. split.
  - intros name Hneeded. unfold FormulaProjection.needed in Hneeded.
    destruct Hneeded as [-> | [-> | [-> | ->]]];apply reference_other;discriminate.
  - repeat split; apply reference_meta_other;lia.
Qed.
Theorem generated_after_prefix_rejected s bs ns (validated : Frame) observations :
  execLocalObserved prefix ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (tt,(validated,observations)) ->
  (19<length (memory (machine validated) arraydef_0__meta))%nat -> meta_value (machine validated) 18=0 ->
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(
    ReplyNOExecution.reply_state (machine validated),observations++[{|flushedOutput:=stdout (machine validated)++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin (machine validated)|}])).
Proof.
  intros Hprefix Hmeta Hvalid. unfold funcdef_0__schemaNode.
  rewrite eliminate_correct,actual_body,prepend_exec. fold prefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish_rejected validated observations Hmeta Hvalid). reflexivity.
Qed.
Theorem generated_after_prefix_overflow s bs ns (validated : Frame) observations :
  execLocalObserved prefix ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (tt,(validated,observations)) ->
  (19<length (memory (machine validated) arraydef_0__meta))%nat ->
  meta_value (machine validated) 18<>0 -> meta_value (machine validated) 16=maximum ->
  execObserved (funcdef_0__schemaNode bs ns) (s,observations)=Some (tt,(store_meta (machine validated) 8 1,observations)).
Proof.
  intros Hprefix Hmeta Hvalid Hfull. unfold funcdef_0__schemaNode.
  rewrite eliminate_correct,actual_body,prepend_exec. fold prefix. rewrite Hprefix. cbn [optionBind fst snd].
  rewrite (generated_finish_overflow validated observations Hmeta Hvalid Hfull). reflexivity.
Qed.
Theorem result_represents s logical raw :
  (19<length (memory s arraydef_0__meta))%nat ->
  SchemaRepresentation.represents s logical ->
  forall expression,
  SchemaRepresentation.entry (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical) raw expression ->
  Z.of_nat (length (Protocol.expressions logical))<maximum ->
  SchemaRepresentation.represents
    (result s (length (Protocol.expressions logical)) raw)
    (SchemaRepresentation.with_expression logical expression).
Proof.
  intros Hmeta Hrep expression Hentry Hword.
  apply (SchemaRepresentation.append s); [exact Hrep|exact Hentry| | |].
  - apply result_nodes. apply SchemaMetadata.represents_length. exact (SchemaRepresentation.metadata s logical Hrep).
  - rewrite Nat.add_1_r. apply result_count. lia.
  - lia.
Qed.
End SchemaNode.
