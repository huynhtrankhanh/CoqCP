From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift ObservedLocal Intern InternReserve InternLengths FormulaCircuit FormulaCircuitProperties
  FormulaCircuitResult FormulaTopology Representation RenameMemoRun RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds
  RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths RenameMemoClassEqual RenameStack AxiomReplacementCircuits SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit SchemaEvaluationIndexCircuitTrace RenameMemoIndexRun.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexReplacementCircuit.
Import IndexExecution SipHashExecution IndexSemantics AxiomReplacementCircuits.
Definition instruction_bound bound instruction := match instruction with
| emit op=>SchemaEvaluationIndexCircuit.operation_bound bound op | map _=>True end.
Section Arena.
Variable arena_bound:nat.
Theorem step s fs ids values p root bound instr q observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+2<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  FormulaCircuit.represents fs ids values -> fits instr -> meaning p values instr=Some q ->
  Z.of_nat (length fs+cost root instr)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) arena_bound ->
  (bound+2<=arena_bound)%nat -> instruction_bound arena_bound instr ->
  exists middle next id, SchemaEvaluationIndexBounds.raw_arena middle (length next) arena_bound /\
    execObserved (native (Z.of_nat root) ids instr) (s,observations)=Some (tt,(middle,observations)) /\
    meta_value middle 0=id /\ NativeRepresentation.canonical_arena middle next /\
    FormulaTopology.ordered middle (length next) /\ meta_value middle 8=0 /\
    FormulaCircuit.represents next (ids++[id]) (values++[q]) /\
    (exists extra,next=fs++extra) /\ (length next<=length fs+cost root instr)%nat /\
    length (memory middle arraydef_0__meta)=length (memory s arraydef_0__meta) /\
    length (memory middle arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hmeaning Hbudget HrawInitial Htarget HinstrBound.
  destruct instr as [op|m].
  - assert (Hinfer:FormulaCircuit.infer [op] values=Some (values++[q])).
    { cbn [FormulaCircuit.infer]. change (FormulaCircuit.meaning values op=Some q) in Hmeaning. now rewrite Hmeaning. }
    assert (Honefits:Forall FormulaCircuit.fits [op]) by (constructor;[exact Hfits|constructor]).
    assert (Honebudget:Z.of_nat (length fs+length [op]+0)<=9223372036854775807) by (cbn [length];change (Z.of_nat (length fs+1)<=9223372036854775807) in Hbudget;lia).
    destruct (FormulaCircuitProperties.complete [op] s fs ids values (values++[q]) 0 observations
      Harena Htopology Herror Hrep Honefits Hinfer Honebudget)
      as (middle & next & result_ids & Htrace & Hframe & Hnext & Hflag & Hnextrep & Hprefix & Hreserve & Hnexttopology & Hgrowth).
    assert (HmiddleRaw:SchemaEvaluationIndexBounds.raw_arena middle (length next) arena_bound).
    { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Harena|exact Herror|exact HrawInitial| | |exact Hnext].
      - cbn [length]. change (Z.of_nat (length fs+1)<=9223372036854775807) in Hbudget. exact Hbudget.
      - constructor;[exact HinstrBound|constructor]. }
    pose proof (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace) as [Hm Hs].
    inversion Htrace;subst. match goal with H:FormulaCircuit.executes _ [] _ _ _ _ |- _=>inversion H;subst end.
    eexists _,_,_. split;[exact HmiddleRaw|]. split;[eassumption|]. split;[reflexivity|]. split;[exact Hnext|]. split;[exact Hnexttopology|].
    split;[exact Hflag|]. split;[exact Hnextrep|]. split;[exact Hprefix|]. split;[exact Hgrowth|]. auto.
  - change (Some (SetTheory.rename (rho m) p)=Some q) in Hmeaning. injection Hmeaning as <-.
    assert (Hmode:mode m=separation_mode \/ mode m=replacement_left_mode \/ mode m=replacement_right_mode \/ mode m=replacement_image_mode)
      by (destruct m;cbn [mode];auto).
    destruct (RenameMemoCallers.fixed_checks bound (mode m) Hmode Hindices) as [Hzeroword Hindexroom].
    assert (Hroom:Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit)
      by (unfold RenameMemoResourceBounds.doubling_limit;rewrite <-Nat2Z.inj_add;exact Hbudget).
    destruct (RenameMemoIndexRun.generated arena_bound s (fun _=>false) (rename_arguments (Z.of_nat root) m)
      fs p root 0 (mode m) 0 0 bound Hmeta Hsip (RenameMemoClassEqual.arena_positive _ _ Harena) Herror Harena Htopology
      Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom Hzeroword Hzeroword Hbound Hindexroom Hheight HrawInitial ltac:(destruct m;cbn [mode RenameMemoIndexBounds.increment];lia) observations)
      as (rframe & next & count & Hrename & Hnext & Hcache & Hword & Hmap & Hsource & Hflag & Hempty & Hgrowth & Hnexttopology & HmiddleRaw).
    rewrite map_result in Hmap. pose proof (RenameMemoOutput.source_extension fs next Hsource) as Hprefix.
    pose proof (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename) as [Hm Hs].
    exists (machine rframe),next,(meta_value (machine rframe) 0). split;[exact HmiddleRaw|]. split;[exact Hrename|]. split;[reflexivity|].
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
  SchemaEvaluationIndexBounds.raw_arena s (length fs) arena_bound ->
  (bound+2<=arena_bound)%nat -> Forall (instruction_bound arena_bound) instructions ->
  exists final next result, SchemaEvaluationIndexBounds.raw_arena final (length next) arena_bound /\
    executes observations (Z.of_nat root) instructions s ids final result /\
    NativeRepresentation.canonical_arena final next /\ FormulaTopology.ordered final (length next) /\ meta_value final 8=0 /\
    FormulaCircuit.represents next result output /\ (exists extra,next=fs++extra) /\
    (length next<=length fs+reserve_cost root instructions)%nat /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\
    length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
    length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  induction instructions as [|instr tail IH] in s,fs,ids,input|-*.
  - intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hinfer Hbudget HrawInitial Htarget HinstrsBound.
    injection Hinfer as <-. exists s,fs,ids. split;[exact HrawInitial|]. split;[constructor|]. split;[exact Harena|]. split;[exact Htopology|].
    split;[exact Herror|]. split;[exact Hrep|]. split;[exists [];now rewrite app_nil_r|].
    split;[cbn [reserve_cost];lia|]. split;[cbn [reserve_cost] in Hbudget;lia|]. auto.
  - intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep Hfits Hinfer Hbudget HrawInitial Htarget HinstrsBound.
    inversion HinstrsBound as [|head rest HinstrBound HtailBound];subst head rest.
    inversion Hfits as [|head rest Hinstr Htailfits];subst head rest.
    cbn [infer] in Hinfer. destruct (meaning p input instr) as [q|] eqn:Hmeaning;[|discriminate].
    assert (Hstepbudget:Z.of_nat (length fs+cost root instr)<=9223372036854775807)
      by (cbn [reserve_cost] in Hbudget;lia).
    destruct (step s fs ids input p root bound instr q observations Hmeta Hsip Harena Htopology Herror Hlookup Hfalse
      Hfuel Hbound Hindices Hheight Hrep Hinstr Hmeaning Hstepbudget HrawInitial Htarget HinstrBound)
      as (middle & middle_fs & id & HmiddleRaw & Hrun & Hvalue & Hmiddle & Hmiddletopology & Hmiddleerror & Hmiddlerep & Hprefix & Hgrowth & Hm & Hs).
    assert (Hmiddlemeta:(31<length (memory middle arraydef_0__meta))%nat) by lia.
    assert (Hmiddlesip:(0<length (memory middle arraydef_0__sipState))%nat) by lia.
    assert (Hmiddlelookup:nth_error middle_fs root=Some p) by (eapply InternReserve.lookup_preserved;eassumption).
    assert (Hmiddlefalse:nth_error middle_fs 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved;eassumption).
    assert (Hremaining:Z.of_nat (length middle_fs+reserve_cost root tail+reserve)<=9223372036854775807)
      by (cbn [reserve_cost] in Hbudget;lia).
    destruct (IH middle middle_fs (ids++[id]) (input++[q]) Hmiddlemeta Hmiddlesip Hmiddle Hmiddletopology Hmiddleerror
      Hmiddlelookup Hmiddlefalse Hfuel Hbound Hindices Hheight Hmiddlerep Htailfits Hinfer Hremaining HmiddleRaw Htarget HtailBound)
      as (final & next & result & HfinalRaw & Htrace & Hnext & Hnexttopology & Hnexterror & Hnextrep & Hnextprefix & Hnextgrowth & Hnextreserve & Hnm & Hns).
    exists final,next,result. split;[exact HfinalRaw|]. split;[econstructor;[exact Hrun|exact Hvalue|lia|exact Htrace]|].
    split;[exact Hnext|]. split;[exact Hnexttopology|]. split;[exact Hnexterror|]. split;[exact Hnextrep|].
    split;[eapply InternReserve.extends_trans;eassumption|]. split;[cbn [reserve_cost];lia|].
    split;[exact Hnextreserve|]. split;lia.
Qed.
End Arena.
End SchemaEvaluationIndexReplacementCircuit.
