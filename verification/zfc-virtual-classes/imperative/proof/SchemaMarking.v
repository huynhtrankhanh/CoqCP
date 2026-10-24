From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaGraph SchemaMetadata InternTail ArrayFacts Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaMarking.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue R.
Ltac drop_statements count code := lazymatch count with
| O=>code
| S ?n=>lazymatch code with bind _ ?next=>let rest:=eval cbn beta in (next tt) in drop_statements n rest end end.
Definition safe_body : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__schemaInstance_body in funcdef_0__schemaInstance_body in
  let code:=drop_statements 1%nat code in
  lazymatch code with bind ?branch _=> lazymatch branch with bind _ ?next=>exact (next false) end end).
Definition remaining : LocalAction unit := ltac:(
  let code:=eval unfold safe_body in safe_body in let rest:=drop_statements 5%nat code in exact rest).
Definition initial_with (work:LocalAction unit) : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__schemaInstance_body in funcdef_0__schemaInstance_body in
  let rest:=eval unfold remaining,safe_body in remaining in
  let family:=eval pattern rest in code in lazymatch family with ?family _=>exact (family work) end).
Lemma actual_initial : funcdef_0__schemaInstance_body=initial_with remaining.
Proof. reflexivity. Qed.
Definition clearing : LocalAction unit := ltac:(
  let code:=eval unfold safe_body in safe_body in let rest:=drop_statements 3%nat code in
  lazymatch rest with bind ?first _=>exact first end).
Definition clear_body total : nat->LocalAction LoopOutcome := ltac:(
  let code:=eval unfold clearing in clearing in lazymatch code with bind _ ?next=>
    let code:=eval cbn beta in (next total) in lazymatch code with loop _ ?body=>exact body end end).
Definition marked_pass : LocalAction unit := ltac:(
  let code:=eval unfold safe_body in safe_body in let rest:=drop_statements 5%nat code in
  lazymatch rest with bind ?first _=>exact first end).
Definition evaluation : LocalAction unit := ltac:(
  let code:=eval unfold safe_body in safe_body in let rest:=drop_statements 6%nat code in exact rest).
Lemma remaining_parts : remaining=(marked_pass >>= fun _=>evaluation).
Proof. reflexivity. Qed.
Definition size root := (SchemaGraph.width root*SchemaGraph.width root)%nat.
Definition grown (s:Machine) root :=
  let m:=withMemory s (growArrays (memory s) arraydef_0__schemaMarks (size root) 0) in
  withMemory m (growArrays (memory m) arraydef_0__schemaValues (size root) 0).
Definition zero (s:Machine) index := withMemory s (modifyArray (memory s) arraydef_0__schemaMarks index 0).
Lemma zero_other s index name : name<>arraydef_0__schemaMarks -> memory (zero s index) name=memory s name.
Proof. intro Hname. unfold zero. cbn [memory withMemory]. now apply InternTailExecution.modify_other. Qed.
Lemma zero_array s index : memory (zero s index) arraydef_0__schemaMarks=<[index:=0]>(memory s arraydef_0__schemaMarks).
Proof. reflexivity. Qed.
Lemma zero_length s index : length (memory (zero s index) arraydef_0__schemaMarks)=length (memory s arraydef_0__schemaMarks).
Proof. rewrite zero_array. apply length_insert. Qed.
Fixpoint clear_many s start count := match count with
| O=>s | S rest=>clear_many (zero s start) (S start) rest end.
Lemma clear_length s start count : length (memory (clear_many s start count) arraydef_0__schemaMarks)=length (memory s arraydef_0__schemaMarks).
Proof. induction count as [|count IH] in s,start|-*;[reflexivity|]. cbn [clear_many]. now rewrite IH,zero_length. Qed.
Lemma clear_other s start count name : name<>arraydef_0__schemaMarks -> memory (clear_many s start count) name=memory s name.
Proof. intro Hname. induction count as [|count IH] in s,start|-*;[reflexivity|]. cbn [clear_many]. now rewrite IH,zero_other by exact Hname. Qed.
Definition cell (s:Machine) index := List.nth index (memory s arraydef_0__schemaMarks) 0.
Lemma clear_outside s start count index : (index<start \/ start+count<=index)%nat ->
  cell (clear_many s start count) index=cell s index.
Proof.
  induction count as [|count IH] in s,start|-*;[reflexivity|]. intro Hindex. cbn [clear_many]. rewrite IH by lia.
  unfold cell. rewrite zero_array. apply ArrayFacts.nth_insert_other. lia.
Qed.
Lemma clear_inside s start count index : (start+count<=length (memory s arraydef_0__schemaMarks))%nat ->
  (start<=index<start+count)%nat -> cell (clear_many s start count) index=0.
Proof.
  induction count as [|count IH] in s,start|-*;[lia|]. intros Hcapacity Hindex. cbn [clear_many].
  destruct (Nat.eq_dec index start) as [->|Hother].
  - rewrite clear_outside by lia. unfold cell. rewrite zero_array. apply OverflowExecution.nth_insert_same. lia.
  - apply IH;[rewrite zero_length;lia|lia].
Qed.
Lemma grown_marks s root : (size root<=length (memory (grown s root) arraydef_0__schemaMarks))%nat.
Proof.
  unfold grown. cbn [memory withMemory]. rewrite growArrays_other by discriminate.
  rewrite growArrays_same,growList_length. lia.
Qed.
Lemma grown_values s root : (size root<=length (memory (grown s root) arraydef_0__schemaValues))%nat.
Proof. unfold grown. cbn [memory withMemory]. rewrite growArrays_same,growList_length. lia. Qed.
Lemma grown_other s root name : name<>arraydef_0__schemaMarks -> name<>arraydef_0__schemaValues -> memory (grown s root) name=memory s name.
Proof. intros Hmarks Hvalues. unfold grown. cbn [memory withMemory]. now rewrite !growArrays_other by assumption. Qed.
Theorem generated_clear_step (f:Frame) total remaining index observations : total-Z.of_nat remaining-1=Z.of_nat index ->
  (index<length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  execLocalObserved (clear_body total remaining) (f,observations)=Some (KeepGoing,(setMachine f (zero (machine f) index),observations)).
Proof.
  intros Hindex Hbound. unfold clear_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite Hindex,Nat2Z.id;exact Hbound)
    |progress rewrite Hindex|progress rewrite Nat2Z.id
    |progress replace (coerceInt 0 8) with 0 by reflexivity
    |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.
Theorem generated_clear_loop count (f:Frame) total start observations : total=Z.of_nat (start+count) ->
  (start+count<=length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  execLocalObserved (loop count (clear_body total)) (f,observations)=Some (tt,(setMachine f (clear_many (machine f) start count),observations)).
Proof.
  induction count as [|count IH] in f,start|-*.
  - intros. destruct f. reflexivity.
  - intros Htotal Hbound. rewrite loop_S,local_bind.
    rewrite (generated_clear_step f total count start observations ltac:(lia) ltac:(lia)). cbn [optionBind fst snd].
    rewrite IH with (start:=S start) by (cbn [machine setMachine];rewrite ?zero_length;lia). destruct f. reflexivity.
Qed.
Definition initialized s root := SchemaGraph.marked (clear_many (grown s root) 0 (size root)) (SchemaGraph.key root root 0).
Definition prepared_frame (f:Frame) root := setMachine
  (setNum (setNum f vardef_0__schemaInstance_width (Z.of_nat (SchemaGraph.width root)))
    vardef_0__schemaInstance_size (Z.of_nat (size root))) (initialized (machine f) root).
Lemma square_division root : Z.of_nat (size root)<=maximum ->
  ~(maximum/Z.of_nat (SchemaGraph.width root)<Z.of_nat (SchemaGraph.width root)).
Proof.
  intro Hsquare. assert (Hwidth:0<Z.of_nat (SchemaGraph.width root)) by (unfold SchemaGraph.width;lia).
  pose proof (Z.div_mod maximum (Z.of_nat (SchemaGraph.width root)) ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound maximum (Z.of_nat (SchemaGraph.width root)) Hwidth) as Hmod.
  unfold size in Hsquare. rewrite Nat2Z.inj_mul in Hsquare. nia.
Qed.
Theorem generated_initial (work:LocalAction unit) (f:Frame) root observations :
  nums f vardef_0__schemaInstance_root=Z.of_nat root -> Z.of_nat (size root)<=maximum ->
  execLocalObserved (initial_with work) (f,observations)=execLocalObserved work (prepared_frame f root,observations).
Proof.
  intros Hroot Hroom.
  assert (Hroot': (let (_,_,ns):=f in ns) vardef_0__schemaInstance_root=Z.of_nat root) by exact Hroot.
  assert (Hwidthpos:0<Z.of_nat (SchemaGraph.width root)) by (unfold SchemaGraph.width;lia).
  assert (Hwidthword:word (Z.of_nat (SchemaGraph.width root))).
  { destruct (SchemaGraph.grid_words root 0 0 ltac:(unfold SchemaGraph.width;lia) ltac:(unfold SchemaGraph.width;lia) Hroom) as [Hword _]. exact Hword. }
  assert (Hwidth:coerceInt (Z.of_nat root+1) 64=Z.of_nat (SchemaGraph.width root)).
  { replace (Z.of_nat root+1) with (Z.of_nat (SchemaGraph.width root)) by (unfold SchemaGraph.width;lia). now apply coerce_word. }
  assert (Hsize:coerceInt (Z.of_nat (SchemaGraph.width root)*Z.of_nat (SchemaGraph.width root)) 64=Z.of_nat (size root)).
  { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word;lia. }
  assert (Hkey:(SchemaGraph.key root root 0<size root)%nat).
  { apply SchemaGraph.grid_bound;unfold SchemaGraph.width;lia. }
  assert (Hclear:forall (middle:Frame), machine middle=grown (machine f) root ->
    execLocalObserved (loop (size root) (clear_body (Z.of_nat (size root)))) (middle,observations)=
      Some (tt,(setMachine middle (clear_many (grown (machine f) root) 0 (size root)),observations))).
  { intros middle Hmachine. rewrite <-Hmachine. apply (generated_clear_loop (size root) middle (Z.of_nat (size root)) 0 observations);[reflexivity|rewrite Hmachine;apply grown_marks]. }
  assert (Hmark:forall (middle:Frame), machine middle=clear_many (grown (machine f) root) 0 (size root) ->
    forall bi ni,ni vardef_0__schemaMark_node=Z.of_nat root -> ni vardef_0__schemaMark_depth=0 ->
      ni vardef_0__schemaMark_width=Z.of_nat (SchemaGraph.width root) ->
      execObserved (funcdef_0__schemaMark bi ni) (machine middle,observations)=Some (tt,(initialized (machine f) root,observations))).
  { intros middle Hmachine bi ni Hnode Hdepth Hstride.
    unfold initialized. rewrite <-Hmachine. apply (SchemaGraph.generated_mark (machine middle) bi ni root 0 (SchemaGraph.width root) observations Hnode Hdepth Hstride).
    - change (Z.of_nat (SchemaGraph.key root root 0)<=maximum). apply Nat2Z.inj_lt in Hkey. lia.
    - change (SchemaGraph.key root root 0<length (memory (machine middle) arraydef_0__schemaMarks))%nat.
      rewrite Hmachine,clear_length. pose proof (grown_marks (machine f) root). lia. }
  unfold initial_with. unfold maximum in *. 
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold addInt at 1|progress unfold multInt at 1|progress unfold divIntUnsigned at 1
    |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
    |progress rewrite Hroot|progress rewrite Hroot'|progress rewrite Hwidth|progress rewrite Hsize|progress rewrite Nat2Z.id
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |match goal with |- context [execLocalObserved (loop ?count ?body) (?middle,observations)] =>
      let expression:=constr:(execLocalObserved (loop count body) (middle,observations)) in
      let Hrun:=fresh in assert (Hrun:expression=Some (tt,(setMachine middle (clear_many (grown (machine f) root) 0 (size root)),observations)))
        by (apply Hclear;reflexivity);rewrite Hrun;clear Hrun end
    |match goal with |- context [execObserved (funcdef_0__schemaMark ?bi ?ni) ?state] =>
      let expression:=constr:(execObserved (funcdef_0__schemaMark bi ni) state) in
      let Hrun:=fresh in assert (Hrun:expression=Some (tt,(initialized (machine f) root,observations)))
        by (apply (SchemaGraph.generated_mark _ bi ni root 0 (SchemaGraph.width root) observations);try reflexivity;
          [change (Z.of_nat (SchemaGraph.key root root 0)<=18446744073709551615);apply Nat2Z.inj_lt in Hkey;lia
          |change (SchemaGraph.key root root 0<length (memory (clear_many (grown (machine f) root) 0 (size root)) arraydef_0__schemaMarks))%nat;
            rewrite clear_length;pose proof (grown_marks (machine f) root);lia]);rewrite Hrun;clear Hrun end
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_false P) by (apply square_division;exact Hroom) end
    |match goal with |- context [decide ?P] => progress rewrite (decide_False (P:=P)) by lia end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  change (optionBind (execLocalObserved work (prepared_frame f root,observations)) (fun r=>Some (tt,snd r))=execLocalObserved work (prepared_frame f root,observations)).
  destruct (execLocalObserved work (prepared_frame f root,observations)) as [[[] after]|];reflexivity.
Qed.
Definition mark_outer_body total : nat->LocalAction LoopOutcome := ltac:(
  let code:=eval unfold marked_pass in marked_pass in lazymatch code with bind _ ?next=>
    let code:=eval cbn beta in (next total) in lazymatch code with loop _ ?body=>exact body end end).
Definition mark_depth_body total : nat->LocalAction LoopOutcome := ltac:(
  let code:=eval unfold mark_outer_body in (mark_outer_body total 0%nat) in
  let code:=eval cbn beta zeta in code in
  lazymatch code with dropWithinLoop (bind _ ?next)=>
    let code:=eval cbn beta in (next tt) in
    lazymatch code with bind (liftToWithinLoop (bind _ ?inner)) _=>
      let code:=eval cbn beta in (inner total) in
      lazymatch code with loop _ ?body=>exact body end end end).
Theorem generated_unmarked_cell (f:Frame) root node depth remaining observations :
  nums f vardef_0__schemaInstance_node=Z.of_nat node ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  Z.of_nat (SchemaGraph.width root)-Z.of_nat remaining-1=Z.of_nat depth ->
  (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
  Z.of_nat (size root)<=maximum -> (size root<=length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  cell (machine f) (SchemaGraph.key root node depth)=0 ->
  execLocalObserved (mark_depth_body (Z.of_nat (SchemaGraph.width root)) remaining) (f,observations)=
  Some (KeepGoing,(setNum f vardef_0__schemaInstance_key (Z.of_nat (SchemaGraph.key root node depth)),observations)).
Proof.
  intros Hnode Hwidth Hdepth Hnb Hdb Hroom Hcapacity Hcell.
  destruct (SchemaGraph.grid_words root node depth Hnb Hdb Hroom) as [Hw [Hp Hkey]].
  assert (Hmul:coerceInt (Z.of_nat node*Z.of_nat (SchemaGraph.width root)) 64=Z.of_nat (node*SchemaGraph.width root))
    by (rewrite Nat2Z.inj_mul;apply coerce_word;exact Hp).
  assert (Hsum:coerceInt (Z.of_nat (node*SchemaGraph.width root)+Z.of_nat depth) 64=Z.of_nat (SchemaGraph.key root node depth))
    by (rewrite <-Nat2Z.inj_add;now apply coerce_word).
  pose proof (SchemaGraph.grid_bound root node depth Hnb Hdb) as Hbound. unfold size in Hcapacity.
  unfold mark_depth_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite Nat2Z.id;lia)
    |progress unfold addInt at 1|progress unfold multInt at 1
    |progress rewrite Hnode|progress rewrite Hwidth|progress rewrite Hdepth
    |progress rewrite Hmul|progress rewrite Hsum|progress rewrite Nat2Z.id
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (coerceInt 0 8) with 0 by reflexivity
    |progress change (List.nth (SchemaGraph.key root node depth) (memory (machine f) arraydef_0__schemaMarks) 0) with (cell (machine f) (SchemaGraph.key root node depth))
    |progress rewrite Hcell
    |progress cbn [nums setNum machine]
    |progress cbn [dropWithinLoop Action_rect bind]
  ]. reflexivity.
Qed.
Fixpoint mark_children (s:Machine) root depth children := match children with
| []=>s
| (child,extra)::rest=>mark_children (SchemaGraph.marked s (SchemaGraph.key root child (depth+extra))) root depth rest
end.
Definition loaded (f:Frame) k a b c d :=
  setNum (setNum (setNum (setNum (setNum f vardef_0__schemaInstance_kind (Z.of_nat k))
    vardef_0__schemaInstance_a (Z.of_nat a)) vardef_0__schemaInstance_b (Z.of_nat b))
    vardef_0__schemaInstance_c (Z.of_nat c)) vardef_0__schemaInstance_d (Z.of_nat d).
Lemma marked_length s index : length (memory (SchemaGraph.marked s index) arraydef_0__schemaMarks)=length (memory s arraydef_0__schemaMarks).
Proof. unfold SchemaGraph.marked. cbn [memory withMemory]. apply length_insert. Qed.
Lemma marked_nodes s index : SchemaMetadata.node_at (SchemaGraph.marked s index)=SchemaMetadata.node_at s.
Proof. unfold SchemaMetadata.node_at. now rewrite SchemaGraph.marked_other by discriminate. Qed.
Lemma initialized_other s root name : name<>arraydef_0__schemaMarks -> name<>arraydef_0__schemaValues ->
  memory (initialized s root) name=memory s name.
Proof. intros Hm Hv. unfold initialized. rewrite SchemaGraph.marked_other by exact Hm.
  rewrite clear_other by exact Hm. now apply grown_other. Qed.
Lemma initialized_capacity s root : (size root<=length (memory (initialized s root) arraydef_0__schemaMarks))%nat.
Proof. unfold initialized. rewrite marked_length,clear_length. apply grown_marks. Qed.
Lemma initialized_cell s root index : (index<size root)%nat ->
  cell (initialized s root) index=if Nat.eqb index (SchemaGraph.key root root 0) then 1 else 0.
Proof.
  intro Hindex. unfold initialized,cell,SchemaGraph.marked. cbn [memory withMemory].
  change (List.nth index (<[SchemaGraph.key root root 0:=1]>(memory (clear_many (grown s root) 0 (size root)) arraydef_0__schemaMarks)) 0 = if Nat.eqb index (SchemaGraph.key root root 0) then 1 else 0).
  destruct (Nat.eq_dec index (SchemaGraph.key root root 0)) as [->|Hneq].
  - rewrite Nat.eqb_refl. apply OverflowExecution.nth_insert_same. rewrite clear_length. pose proof (grown_marks s root). lia.
  - rewrite ArrayFacts.nth_insert_other by exact Hneq. rewrite (proj2 (Nat.eqb_neq _ _) Hneq).
    change (cell (clear_many (grown s root) 0 (size root)) index=0).
    apply clear_inside;[apply grown_marks|lia].
Qed.
Theorem generated_marked_cell (f:Frame) root node depth remaining k a b c d x y observations :
  nums f vardef_0__schemaInstance_node=Z.of_nat node ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  Z.of_nat (SchemaGraph.width root)-Z.of_nat remaining-1=Z.of_nat depth ->
  (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
  Z.of_nat (size root)<=maximum -> (size root<=length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  (node<length (memory (machine f) arraydef_0__schemaNodes))%nat ->
  SchemaMetadata.node_at (machine f) node=(Z.of_nat k,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,x,y) ->
  cell (machine f) (SchemaGraph.key root node depth)<>0 ->
  (forall child extra, In (child,extra) (SchemaGraph.children_fields k a b c d) ->
    (SchemaGraph.key root child (depth+extra)<size root)%nat) ->
  execLocalObserved (mark_depth_body (Z.of_nat (SchemaGraph.width root)) remaining) (f,observations)=
  Some (KeepGoing,(setMachine (loaded (setNum f vardef_0__schemaInstance_key (Z.of_nat (SchemaGraph.key root node depth))) k a b c d)
    (mark_children (machine f) root depth (SchemaGraph.children_fields k a b c d)),observations)).
Proof.
  intros Hnode Hwidth Hdepth Hnb Hdb Hroom Hcapacity Hnodes Hraw Hcell Hdep.
  assert (Hnode':(let (_,_,ns):=f in ns) vardef_0__schemaInstance_node=Z.of_nat node) by exact Hnode.
  assert (Hwidth':(let (_,_,ns):=f in ns) vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)) by exact Hwidth.
  destruct (SchemaGraph.grid_words root node depth Hnb Hdb Hroom) as [Hw [Hp Hkey]].
  assert (Hmul:coerceInt (Z.of_nat node*Z.of_nat (SchemaGraph.width root)) 64=Z.of_nat (node*SchemaGraph.width root))
    by (rewrite Nat2Z.inj_mul;apply coerce_word;exact Hp).
  assert (Hsum:coerceInt (Z.of_nat (node*SchemaGraph.width root)+Z.of_nat depth) 64=Z.of_nat (SchemaGraph.key root node depth))
    by (rewrite <-Nat2Z.inj_add;now apply coerce_word).
  assert (Hplus:coerceInt (Z.of_nat depth+1) 64=Z.of_nat (depth+1)).
  { replace (Z.of_nat depth+1) with (Z.of_nat (depth+1)) by lia. apply coerce_word. unfold word.
    unfold size,SchemaGraph.width in Hroom,Hdb. rewrite Nat2Z.inj_mul in Hroom. nia. }
  pose proof (SchemaGraph.grid_bound root node depth Hnb Hdb) as Hbound.
  unfold SchemaMetadata.node_at in Hraw. unfold size in Hcapacity.
  assert (Hmark:forall s bi ni child extra,
    In (child,extra) (SchemaGraph.children_fields k a b c d) ->
    length (memory s arraydef_0__schemaMarks)=length (memory (machine f) arraydef_0__schemaMarks) ->
    ni vardef_0__schemaMark_node=Z.of_nat child ->
    ni vardef_0__schemaMark_depth=Z.of_nat (depth+extra) ->
    ni vardef_0__schemaMark_width=Z.of_nat (SchemaGraph.width root) ->
    execObserved (funcdef_0__schemaMark bi ni) (s,observations)=
      Some (tt,(SchemaGraph.marked s (SchemaGraph.key root child (depth+extra)),observations))).
  { intros s bi ni child extra Hin Hlen Hcn Hcd Hcw.
    pose proof (Hdep child extra Hin) as Hcb. apply (SchemaGraph.generated_mark s bi ni child (depth+extra) (SchemaGraph.width root) observations Hcn Hcd Hcw).
    - change (Z.of_nat (SchemaGraph.key root child (depth+extra))<=maximum). apply Nat2Z.inj_lt in Hcb. lia.
    - change (SchemaGraph.key root child (depth+extra)<length (memory s arraydef_0__schemaMarks))%nat.
      rewrite Hlen. unfold size in Hcb. lia. }
  unfold mark_depth_body,loaded.
  repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite Nat2Z.id;lia)
    |progress unfold addInt at 1|progress unfold multInt at 1
    |progress rewrite Hnode|progress rewrite Hwidth|progress rewrite Hnode'|progress rewrite Hwidth'|progress rewrite Hdepth
    |progress rewrite Hmul|progress rewrite Hsum|progress rewrite Hplus|progress rewrite Nat2Z.id
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (coerceInt 0 8) with 0 by reflexivity
    |progress change (List.nth (SchemaGraph.key root node depth) (memory (machine f) arraydef_0__schemaMarks) 0) with (cell (machine f) (SchemaGraph.key root node depth))
    |progress rewrite (bool_decide_true (cell (machine f) (SchemaGraph.key root node depth)<>0)) by exact Hcell
    |progress rewrite Hraw
    |progress cbn [nums setNum setMachine machine]
    |progress cbn [bind]
  ].
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]].
  all: cbn [SchemaGraph.children_fields] in Hdep |- *.
  all: repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite Nat2Z.id;lia)
    |progress unfold addInt at 1
    |progress rewrite Hwidth|progress rewrite Hwidth'|progress rewrite Hplus
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress cbn [nums setNum setMachine machine]
    |match goal with |- context [execObserved (funcdef_0__schemaMark ?bi ?ni) (?native,?trace)] =>
      lazymatch ni with update (update (update _ vardef_0__schemaMark_node (Z.of_nat ?child)) vardef_0__schemaMark_depth _) vardef_0__schemaMark_width _ =>
      first [
        let Hrun:=fresh in
        assert (Hrun:execObserved (funcdef_0__schemaMark bi ni) (native,trace)=
          Some (tt,(SchemaGraph.marked native (SchemaGraph.key root child (depth+1)),trace)))
        by (eapply Hmark with (extra:=1%nat);[cbn;auto|now rewrite ?marked_length|reflexivity|reflexivity|reflexivity]);
        rewrite Hrun;clear Hrun
      | let Hrun:=fresh in
        assert (Hrun:execObserved (funcdef_0__schemaMark bi ni) (native,trace)=
          Some (tt,(SchemaGraph.marked native (SchemaGraph.key root child (depth+0)),trace)))
        by (eapply Hmark with (extra:=0%nat);[cbn;auto|now rewrite ?marked_length|reflexivity|now rewrite Nat.add_0_r|reflexivity]);
        rewrite Hrun;clear Hrun]
      end end
    |progress rewrite Nat.add_0_r
    |progress cbn [bind]
    |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
  ].
all: cbn [SchemaGraph.need_p SchemaGraph.need_q SchemaGraph.need_r existsb Nat.eqb mark_children app];rewrite ?Nat.add_0_r.
all: try (destruct f;reflexivity).
  destruct a as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|a]]]]]]]]]]]]]]]]].
  all: cbn [SchemaGraph.need_p SchemaGraph.need_q SchemaGraph.need_r] in Hdep,Hmark |- *.
  all: repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite Nat2Z.id;lia)
    |progress unfold addInt at 1
    |progress rewrite Hwidth|progress rewrite Hwidth'|progress rewrite Hplus
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress cbn [nums setNum setMachine machine]
    |match goal with |- context [execObserved (funcdef_0__schemaMark ?bi ?ni) (?native,?trace)] =>
      lazymatch ni with update (update (update _ vardef_0__schemaMark_node (Z.of_nat ?child)) vardef_0__schemaMark_depth _) vardef_0__schemaMark_width _ =>
      first [
        let Hrun:=fresh in
        assert (Hrun:execObserved (funcdef_0__schemaMark bi ni) (native,trace)=
          Some (tt,(SchemaGraph.marked native (SchemaGraph.key root child (depth+1)),trace)))
        by (eapply Hmark with (extra:=1%nat);[cbn;auto|now rewrite ?marked_length|reflexivity|reflexivity|reflexivity]);
        rewrite Hrun;clear Hrun
      | let Hrun:=fresh in
        assert (Hrun:execObserved (funcdef_0__schemaMark bi ni) (native,trace)=
          Some (tt,(SchemaGraph.marked native (SchemaGraph.key root child (depth+0)),trace)))
        by (eapply Hmark with (extra:=0%nat);[cbn;auto|now rewrite ?marked_length|reflexivity|now rewrite Nat.add_0_r|reflexivity]);
        rewrite Hrun;clear Hrun]
      end end
    |progress rewrite Nat.add_0_r
    |progress cbn [bind]
    |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
  ].
  all: cbn [SchemaGraph.need_p SchemaGraph.need_q SchemaGraph.need_r existsb Nat.eqb mark_children app];rewrite ?Nat.add_0_r.
  all: try (destruct f;reflexivity).
all: try (repeat rewrite Nat.add_0_r;destruct f;reflexivity).
all: cbn [orb dropWithinLoop Action_rect execLocalObserved mark_children app].
all: rewrite ?Nat.add_0_r;destruct f;reflexivity.
Qed.
End SchemaMarking.
