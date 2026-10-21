From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayFacts RenameMemoBuffers RenameMemoProbe RenameMemoLookup
  RenameMemoRebuild RenameMemoRebuildInvariant ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoResize.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers.
Local Opaque funcdef_0__formulaHash hash_state.
Definition scratch_grown (s : Machine) size := withMemory s (growArrays (memory s) arraydef_0__renameMemoScratch size (0,0,0,0)).
Definition memo_grown (s : Machine) size := withMemory s (growArrays (memory s) arraydef_0__renameMemo size (0,0,0,0)).
Lemma scratch_grown_array s size : memory (scratch_grown s size) arraydef_0__renameMemoScratch=
  growList (memory s arraydef_0__renameMemoScratch) size (0,0,0,0).
Proof. reflexivity. Qed.
Lemma memo_grown_array s size : memory (memo_grown s size) arraydef_0__renameMemo=
  growList (memory s arraydef_0__renameMemo) size (0,0,0,0).
Proof. reflexivity. Qed.
Lemma scratch_grown_other s size name : name<>arraydef_0__renameMemoScratch -> memory (scratch_grown s size) name=memory s name.
Proof. destruct name; intro Hname; try congruence; reflexivity. Qed.
Lemma memo_grown_other s size name : name<>arraydef_0__renameMemo -> memory (memo_grown s size) name=memory s name.
Proof. destruct name; intro Hname; try congruence; reflexivity. Qed.
Lemma scratch_capacity s size : (size<=length (memory (scratch_grown s size) arraydef_0__renameMemoScratch))%nat.
Proof. rewrite scratch_grown_array,growList_length. lia. Qed.
Lemma memo_capacity s size : (size<=length (memory (memo_grown s size) arraydef_0__renameMemo))%nat.
Proof. rewrite memo_grown_array,growList_length. lia. Qed.
Definition start_frame (f : Frame) count :=
  setMachine (setNum (setNum f vardef_0__renameCacheGrow_oldSize (Z.of_nat count))
    vardef_0__renameCacheGrow_size (Z.of_nat (2*count))) (scratch_grown (machine f) (2*count)).
Definition copy_start (f : Frame) size := setMachine f (memo_grown (machine f) size).
Definition finish (f : Frame) size := setMachine f (store_meta (machine f) 29 (Z.of_nat size)).
Lemma double_word count : Z.of_nat count<=9223372036854775807 -> word (Z.of_nat count*2).
Proof. unfold word,maximum. lia. Qed.
Lemma double_value count : Z.of_nat count*2=Z.of_nat (2*count).
Proof. rewrite Nat2Z.inj_mul. cbn. lia. Qed.
Theorem generated_composition clear rebuild copy (f cleared rebuilt copied : Frame) count observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 29=Z.of_nat count ->
  Z.of_nat count<=9223372036854775807 ->
  execLocalObserved (clear (Z.of_nat (2*count))) (start_frame f count,observations)=Some (tt,(cleared,observations)) ->
  nums cleared vardef_0__renameCacheGrow_oldSize=Z.of_nat count -> nums cleared vardef_0__renameCacheGrow_size=Z.of_nat (2*count) ->
  execLocalObserved (rebuild (Z.of_nat count)) (cleared,observations)=Some (tt,(rebuilt,observations)) ->
  nums rebuilt vardef_0__renameCacheGrow_size=Z.of_nat (2*count) -> meta_value (machine rebuilt) 8=0 ->
  (31<length (memory (machine rebuilt) arraydef_0__meta))%nat ->
  execLocalObserved (copy (Z.of_nat (2*count))) (copy_start rebuilt (2*count),observations)=Some (tt,(copied,observations)) ->
  nums copied vardef_0__renameCacheGrow_size=Z.of_nat (2*count) ->
  (31<length (memory (machine copied) arraydef_0__meta))%nat ->
  execLocalObserved (body_with clear rebuild copy) (f,observations)=Some (tt,(finish copied (2*count),observations)).
Proof.
  intros Hmeta Hcount Hword Hclear Hcold Hcsize Hrebuild Hrsize Herror Hrmeta Hcopy Hpsize Hpmeta.
  destruct f as [s bs ns],cleared as [cs cbs cns],rebuilt as [rs rbs rns],copied as [ps pbs pns].
  cbn [machine nums] in *. unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];
       first [eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta]
             |eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hrmeta]
             |eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hpmeta]])
    |progress replace (Z.to_nat 29) with 29%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Hcold |progress rewrite Hcsize
    |progress rewrite Hrsize |progress rewrite Herror |progress rewrite Hpsize
    |progress rewrite (coerce_word _ (double_word count Hword))
    |progress rewrite double_value |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by reflexivity
       |progress rewrite (bool_decide_false P) by lia] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools multInt
       Imperative.update decide decide_rel
       variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow varsfuncdef_0__renameCacheGrow_rec]
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (?callee ?n) ?state] =>
       first [constr_eq callee clear|constr_eq callee rebuild|constr_eq callee copy];
       let expression:=constr:(@execLocalObserved I T EI V EV R (callee n) state) in
       let Hrun:=fresh "Hrun" in first
         [assert (Hrun : expression=Some (tt,({|machine:=cs;bools:=cbs;nums:=cns|},observations))) by exact Hclear
         |assert (Hrun : expression=Some (tt,({|machine:=rs;bools:=rbs;nums:=rns|},observations))) by exact Hrebuild
         |assert (Hrun : expression=Some (tt,({|machine:=ps;bools:=pbs;nums:=pns|},observations))) by exact Hcopy];
       rewrite Hrun; clear Hrun end
  ]. reflexivity.
Qed.
Theorem generated_overflow s bs ns observations : (31<length (memory s arraydef_0__meta))%nat ->
  9223372036854775807<meta_value s 29 ->
  execObserved (funcdef_0__renameCacheGrow bs ns) (s,observations)=Some (tt,(store_meta s 8 1,observations)).
Proof.
  intros Hmeta Hoverflow. unfold funcdef_0__renameCacheGrow. rewrite ObservedLocal.eliminate_correct.
  unfold funcdef_0__renameCacheGrow_body.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];
       eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta])
    |progress replace (Z.to_nat 29) with 29%nat by reflexivity
    |progress rewrite bool_decide_true by exact Hoverflow
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools
       Imperative.update decide decide_rel
       variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow varsfuncdef_0__renameCacheGrow_rec]
  ]. reflexivity.
Qed.
End RenameMemoResize.
