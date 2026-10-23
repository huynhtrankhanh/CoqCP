From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal Intern InternReserve InternLengths FormulaCircuit FormulaCircuitProperties
  FormulaCircuitResult FormulaTopology Representation RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds
  RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths RenameMemoClassEqual RenameStack.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomReplacementCircuits.
Import IndexExecution SipHashExecution IndexSemantics.
Inductive mapping := left | right | image.
Definition mode m := match m with left=>replacement_left_mode | right=>replacement_right_mode | image=>replacement_image_mode end.
Definition rho m := match m with left=>SetTheory.repl_left | right=>SetTheory.repl_right | image=>SetTheory.repl_image end.
Inductive instruction := emit (op:FormulaCircuit.operation) | map (m:mapping).
Definition plan := [emit (FormulaCircuit.member 0 1);map left;map right;emit (FormulaCircuit.equal 1 0);
  emit (FormulaCircuit.implies 3 4);emit (FormulaCircuit.implies 2 5);emit (FormulaCircuit.all 6);
  emit (FormulaCircuit.all 7);emit (FormulaCircuit.implies 1 8);emit (FormulaCircuit.all 9);
  emit (FormulaCircuit.member 0 3);map image;emit (FormulaCircuit.implies 12 0);
  emit (FormulaCircuit.implies 11 13);emit (FormulaCircuit.implies 14 0);emit (FormulaCircuit.implies 15 0);
  emit (FormulaCircuit.all 16);emit (FormulaCircuit.implies 17 0);emit (FormulaCircuit.implies 18 1);
  emit (FormulaCircuit.all 19);emit (FormulaCircuit.implies 20 0);emit (FormulaCircuit.all 21);
  emit (FormulaCircuit.implies 22 0);emit (FormulaCircuit.implies 10 23)].
Definition rename_arguments root m : varsfuncdef_0__rename -> Z :=
  update (update (update (update (fun _=>0) vardef_0__rename_node root)
    vardef_0__rename_mode (mode_number (mode m))) vardef_0__rename_shift 0) vardef_0__rename_arg 0.
Definition native root ids instr := match instr with
| emit op=>funcdef_0__intern (fun _=>false) (FormulaCircuit.parameters ids op)
| map m=>funcdef_0__rename (fun _=>false) (rename_arguments root m) end.
Definition meaning p values instr := match instr with
| emit op=>FormulaCircuit.meaning values op
| map m=>Some (SetTheory.rename (rho m) p) end.
Fixpoint infer p instructions values := match instructions with
| []=>Some values | instr::tail=>optionBind (meaning p values instr) (fun q=>infer p tail (values++[q])) end.
Definition values p := match infer p plan [SetTheory.falsity] with Some result=>result | None=>[] end.
Lemma inferred p : infer p plan [SetTheory.falsity]=Some (values p).
Proof. reflexivity. Qed.
Lemma target p : nth_error (values p) 24=Some (SetTheory.replacement p).
Proof. reflexivity. Qed.
Inductive executes observations root : list instruction -> Machine -> list Z -> Machine -> list Z -> Prop :=
| finished s ids : executes observations root [] s ids s ids
| emitted instr tail s ids middle id final result :
    execObserved (native root ids instr) (s,observations)=Some (tt,(middle,observations)) ->
    meta_value middle 0=id -> (0<length (memory middle arraydef_0__meta))%nat ->
    executes observations root tail middle (ids++[id]) final result ->
    executes observations root (instr::tail) s ids final result.
Lemma last_slot observations root instructions s ids final result : executes observations root instructions s ids final result ->
  instructions<>[] -> nth_error result (length ids+length instructions-1)=Some (meta_value final 0).
Proof.
  intro Htrace. induction Htrace as [s ids|instr tail s ids middle id final result Hrun Hvalue Hmeta Htail IH].
  - contradiction.
  - intro Hnonempty. destruct tail as [|head rest].
    + inversion Htail;subst. cbn [length]. replace (length ids+1-1)%nat with (length ids) by lia.
      rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn [nth_error]. reflexivity.
    + specialize (IH ltac:(discriminate)). rewrite length_app in IH. cbn [length] in IH |- *.
      replace (length ids+S (S (length rest))-1)%nat with (length ids+1+S (length rest)-1)%nat by lia. exact IH.
Qed.
Theorem result observations root s final ids next p : executes observations root plan s [0] final ids ->
  FormulaCircuit.represents next ids (values p) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.replacement p) /\
  SetTheory.derives (SetTheory.replacement p).
Proof.
  intros Htrace Hrep. pose proof (FormulaCircuit.wire next ids (values p) 24 (SetTheory.replacement p) Hrep (target p)) as Hmeaning.
  pose proof (last_slot _ _ _ _ _ _ _ Htrace ltac:(discriminate)) as Hlast.
  change (nth_error ids 24=Some (meta_value final 0)) in Hlast.
  rewrite (List.nth_error_nth _ _ 0 Hlast) in Hmeaning. split;[exact (proj1 Hmeaning)|].
  split;[exact (proj2 Hmeaning)|apply SetTheory.d_set,SetTheory.ax_replacement].
Qed.


Definition fits instr := match instr with emit op=>FormulaCircuit.fits op | map _=>True end.
Lemma plan_fits : Forall fits plan.
Proof. unfold plan;repeat (constructor;[first [exact I|unfold fits,FormulaCircuit.fits,word,maximum;lia]|]);constructor. Qed.
Definition cost root instr := match instr with emit _=>1%nat | map _=>(S root*S root)%nat end.
Fixpoint reserve_cost root instructions := match instructions with []=>0%nat | i::tail=>(cost root i+reserve_cost root tail)%nat end.
Lemma map_result m p : RenameStack.renamed (renaming (mode m) 0 0) 0 p=SetTheory.rename (rho m) p.
Proof. destruct m;reflexivity. Qed.
Theorem step s fs ids values p root bound instr q observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+2<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  FormulaCircuit.represents fs ids values -> fits instr -> meaning p values instr=Some q ->
  Z.of_nat (length fs+cost root instr)<=9223372036854775807 ->
  exists middle next id,
    execObserved (native (Z.of_nat root) ids instr) (s,observations)=Some (tt,(middle,observations)) /\
    meta_value middle 0=id /\ NativeRepresentation.canonical_arena middle next /\
    FormulaTopology.ordered middle (length next) /\ meta_value middle 8=0 /\
    FormulaCircuit.represents next (ids++[id]) (values++[q]) /\
    (exists extra,next=fs++extra) /\ (length next<=length fs+cost root instr)%nat /\
    length (memory middle arraydef_0__meta)=length (memory s arraydef_0__meta) /\
    length (memory middle arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hmeaning Hbudget.
  destruct instr as [op|m].
  - assert (Hinfer:FormulaCircuit.infer [op] values=Some (values++[q])).
    { cbn [FormulaCircuit.infer]. change (FormulaCircuit.meaning values op=Some q) in Hmeaning. now rewrite Hmeaning. }
    assert (Honefits:Forall FormulaCircuit.fits [op]) by (constructor;[exact Hfits|constructor]).
    assert (Honebudget:Z.of_nat (length fs+length [op]+0)<=9223372036854775807) by (cbn [length];change (Z.of_nat (length fs+1)<=9223372036854775807) in Hbudget;lia).
    destruct (FormulaCircuitProperties.complete [op] s fs ids values (values++[q]) 0 observations
      Harena Htopology Herror Hrep Honefits Hinfer Honebudget)
      as (middle & next & result_ids & Htrace & Hframe & Hnext & Hflag & Hnextrep & Hprefix & Hreserve & Hnexttopology & Hgrowth).
    pose proof (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace) as [Hm Hs].
    inversion Htrace;subst. match goal with H:FormulaCircuit.executes _ [] _ _ _ _ |- _=>inversion H;subst end.
    eexists _,_,_. split;[eassumption|]. split;[reflexivity|]. split;[exact Hnext|]. split;[exact Hnexttopology|].
    split;[exact Hflag|]. split;[exact Hnextrep|]. split;[exact Hprefix|]. split;[exact Hgrowth|]. auto.
  - change (Some (SetTheory.rename (rho m) p)=Some q) in Hmeaning. injection Hmeaning as <-.
    assert (Hmode:mode m=separation_mode \/ mode m=replacement_left_mode \/ mode m=replacement_right_mode \/ mode m=replacement_image_mode)
      by (destruct m;cbn [mode];auto).
    destruct (RenameMemoCallers.fixed_checks bound (mode m) Hmode Hindices) as [Hzeroword Hindexroom].
    assert (Hroom:Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit)
      by (unfold RenameMemoResourceBounds.doubling_limit;rewrite <-Nat2Z.inj_add;exact Hbudget).
    destruct (RenameMemoRun.generated s (fun _=>false) (rename_arguments (Z.of_nat root) m)
      fs p root 0 (mode m) 0 0 bound Hmeta Hsip (RenameMemoClassEqual.arena_positive _ _ Harena) Herror Harena Htopology
      Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom Hzeroword Hzeroword Hbound Hindexroom Hheight observations)
      as (rframe & next & count & Hrename & Hnext & Hcache & Hword & Hmap & Hsource & Hflag & Hempty & Hgrowth & Hnexttopology).
    rewrite map_result in Hmap. pose proof (RenameMemoOutput.source_extension fs next Hsource) as Hprefix.
    pose proof (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename) as [Hm Hs].
    exists (machine rframe),next,(meta_value (machine rframe) 0). split;[exact Hrename|]. split;[reflexivity|].
    split;[exact Hnext|]. split;[exact Hnexttopology|]. split;[exact Hflag|]. split.
    + apply Forall2_app;[eapply FormulaCircuit.extend;eassumption|]. constructor;[split;assumption|constructor].
    + split;[exact Hprefix|]. split;[exact Hgrowth|]. auto.
Qed.


Theorem complete instructions s fs ids input p root bound output reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+2<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  FormulaCircuit.represents fs ids input -> Forall fits instructions -> infer p instructions input=Some output ->
  Z.of_nat (length fs+reserve_cost root instructions+reserve)<=9223372036854775807 ->
  exists final next result,
    executes observations (Z.of_nat root) instructions s ids final result /\
    NativeRepresentation.canonical_arena final next /\ FormulaTopology.ordered final (length next) /\ meta_value final 8=0 /\
    FormulaCircuit.represents next result output /\ (exists extra,next=fs++extra) /\
    (length next<=length fs+reserve_cost root instructions)%nat /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\
    length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
    length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  induction instructions as [|instr tail IH] in s,fs,ids,input|-*.
  - intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hinfer Hbudget.
    injection Hinfer as <-. exists s,fs,ids. split;[constructor|]. split;[exact Harena|]. split;[exact Htopology|].
    split;[exact Herror|]. split;[exact Hrep|]. split;[exists [];now rewrite app_nil_r|].
    split;[cbn [reserve_cost];lia|]. split;[cbn [reserve_cost] in Hbudget;lia|]. auto.
  - intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hinfer Hbudget.
    inversion Hfits as [|head rest Hinstr Htailfits];subst head rest.
    cbn [infer] in Hinfer. destruct (meaning p input instr) as [q|] eqn:Hmeaning;[|discriminate].
    assert (Hstepbudget:Z.of_nat (length fs+cost root instr)<=9223372036854775807)
      by (cbn [reserve_cost] in Hbudget;lia).
    destruct (step s fs ids input p root bound instr q observations Hmeta Hsip Harena Htopology Herror Hlookup Hfalse
      Hfuel Hbound Hindices Hheight Hrep Hinstr Hmeaning Hstepbudget)
      as (middle & middle_fs & id & Hrun & Hvalue & Hmiddle & Hmiddletopology & Hmiddleerror & Hmiddlerep & Hprefix & Hgrowth & Hm & Hs).
    assert (Hmiddlemeta:(31<length (memory middle arraydef_0__meta))%nat) by lia.
    assert (Hmiddlesip:(0<length (memory middle arraydef_0__sipState))%nat) by lia.
    assert (Hmiddlelookup:nth_error middle_fs root=Some p) by (eapply InternReserve.lookup_preserved;eassumption).
    assert (Hmiddlefalse:nth_error middle_fs 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved;eassumption).
    assert (Hremaining:Z.of_nat (length middle_fs+reserve_cost root tail+reserve)<=9223372036854775807)
      by (cbn [reserve_cost] in Hbudget;lia).
    destruct (IH middle middle_fs (ids++[id]) (input++[q]) Hmiddlemeta Hmiddlesip Hmiddle Hmiddletopology Hmiddleerror
      Hmiddlelookup Hmiddlefalse Hfuel Hbound Hindices Hheight Hmiddlerep Htailfits Hinfer Hremaining)
      as (final & next & result & Htrace & Hnext & Hnexttopology & Hnexterror & Hnextrep & Hnextprefix & Hnextgrowth & Hnextreserve & Hnm & Hns).
    exists final,next,result. split;[econstructor;[exact Hrun|exact Hvalue|lia|exact Htrace]|].
    split;[exact Hnext|]. split;[exact Hnexttopology|]. split;[exact Hnexterror|]. split;[exact Hnextrep|].
    split;[eapply InternReserve.extends_trans;eassumption|]. split;[cbn [reserve_cost];lia|].
    split;[exact Hnextreserve|]. split;lia.
Qed.
End AxiomReplacementCircuits.
