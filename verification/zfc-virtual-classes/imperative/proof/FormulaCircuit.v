From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternReserve FormulaEncoding Representation NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module FormulaCircuit.
Import IndexExecution SipHashExecution.
Inductive operation := equal (i j : nat) | member (i j : nat) | implies (left right : nat) | all (body : nat).
Definition arguments tag a b : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _=>0) vardef_0__intern_tag tag) vardef_0__intern_a a) vardef_0__intern_b b.
Definition parameters ids op := match op with
| equal i j => arguments 1 (Z.of_nat i) (Z.of_nat j)
| member i j => arguments 2 (Z.of_nat i) (Z.of_nat j)
| implies p q => arguments 3 (List.nth p ids 0) (List.nth q ids 0)
| all p => arguments 4 (List.nth p ids 0) 0 end.
Definition meaning values op := match op with
| equal i j => Some (SetTheory.equal i j)
| member i j => Some (SetTheory.member i j)
| implies p q => optionBind (nth_error values p) (fun a=>option_map (SetTheory.implies a) (nth_error values q))
| all p => option_map SetTheory.all (nth_error values p) end.
Definition fits op := match op with
| equal i j | member i j => word (Z.of_nat i) /\ word (Z.of_nat j)
| _ => True end.
Definition represents (fs : list SetTheory.formula) ids values := Forall2 (fun id value => word id /\ nth_error fs (Z.to_nat id) = Some value) ids values.
Lemma wire fs ids values index value : represents fs ids values -> nth_error values index = Some value ->
  word (List.nth index ids 0) /\ nth_error fs (Z.to_nat (List.nth index ids 0)) = Some value.
Proof.
  intros Hrep Hvalue. destruct (NameRepresentation.related_lookup _ _ _ index value Hrep Hvalue) as [id [Hid Hmeaning]].
  now rewrite (List.nth_error_nth _ _ 0 Hid).
Qed.
Lemma extend fs next ids values : (exists extra,next=fs++extra) -> represents fs ids values -> represents next ids values.
Proof.
  intros Hprefix Hrep. eapply Forall2_impl; [exact Hrep|]. intros id value [Hword Hlookup]. split; [exact Hword|]. eapply InternReserve.lookup_preserved; eassumption.
Qed.
Lemma decode fs ids values op p : represents fs ids values -> fits op -> meaning values op = Some p ->
  FormulaEncoding.normal (parameters ids op vardef_0__intern_tag,parameters ids op vardef_0__intern_a,parameters ids op vardef_0__intern_b) /\
  FormulaEncoding.decode fs (parameters ids op vardef_0__intern_tag,parameters ids op vardef_0__intern_a,parameters ids op vardef_0__intern_b) = Some p.
Proof.
  intros Hrep Hfits Hmeaning. destruct op as [i j|i j|i j|i]; cbn [meaning] in Hmeaning.
  - injection Hmeaning as <-. change (FormulaEncoding.normal (1,Z.of_nat i,Z.of_nat j) /\ FormulaEncoding.decode fs (1,Z.of_nat i,Z.of_nat j) = Some (SetTheory.equal i j)).
    split; [right; left; auto|]. cbn [FormulaEncoding.decode]. now rewrite !Nat2Z.id.
  - injection Hmeaning as <-. change (FormulaEncoding.normal (2,Z.of_nat i,Z.of_nat j) /\ FormulaEncoding.decode fs (2,Z.of_nat i,Z.of_nat j) = Some (SetTheory.member i j)).
    split; [right; left; auto|]. cbn [FormulaEncoding.decode]. now rewrite !Nat2Z.id.
  - destruct (nth_error values i) as [a|] eqn:Ha; [|discriminate]. destruct (nth_error values j) as [b|] eqn:Hb; [|discriminate]. injection Hmeaning as <-.
    destruct (wire fs ids values i a Hrep Ha) as [Hai Hlookup_a]. destruct (wire fs ids values j b Hrep Hb) as [Hbi Hlookup_b].
    change (FormulaEncoding.normal (3,List.nth i ids 0,List.nth j ids 0) /\ FormulaEncoding.decode fs (3,List.nth i ids 0,List.nth j ids 0) = Some (SetTheory.implies a b)).
    split; [right; left; auto|]. cbn [FormulaEncoding.decode]. now rewrite Hlookup_a,Hlookup_b.
  - destruct (nth_error values i) as [a|] eqn:Ha; [|discriminate]. injection Hmeaning as <-.
    destruct (wire fs ids values i a Hrep Ha) as [Hai Hlookup_a].
    change (FormulaEncoding.normal (4,List.nth i ids 0,0) /\ FormulaEncoding.decode fs (4,List.nth i ids 0,0) = Some (SetTheory.all a)).
    split; [right; right; auto|]. cbn [FormulaEncoding.decode]. now rewrite Hlookup_a.
Qed.
Theorem step s fs ids values op p reserve observations : NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 ->
  represents fs ids values -> fits op -> meaning values op = Some p ->
  Z.of_nat (length fs + S reserve) <= 9223372036854775807 ->
  exists final next index, execObserved (funcdef_0__intern (fun _=>false) (parameters ids op)) (s,observations) = Some (tt,(final,observations)) /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\ meta_value final 8 = 0 /\
    meta_value final 0 = Z.of_nat index /\ represents next (ids ++ [Z.of_nat index]) (values ++ [p]) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  intros Harena Herror Hrep Hfits Hmeaning Hbudget. destruct (decode fs ids values op p Hrep Hfits Hmeaning) as [Hnormal Hdecode].
  destruct (InternReserve.generated_refines s (fun _=>false) (parameters ids op) fs p reserve observations Harena Herror Hbudget Hnormal Hdecode)
    as [final [next [index [Hrun [Hframe [Hnext [Hflag [Hindex [Hword [Hlookup [Hprefix Hreserve]]]]]]]]]]].
  exists final,next,index. split; [exact Hrun|]. split; [exact Hframe|]. split; [exact Hnext|]. split; [exact Hflag|]. split; [exact Hindex|]. split.
  - apply Forall2_app; [eapply extend; eassumption|]. constructor; [|constructor]. split; [exact Hword|]. now rewrite Nat2Z.id.
  - split; assumption.
Qed.
Fixpoint infer plan values := match plan with
| [] => Some values
| op::tail => optionBind (meaning values op) (fun p=>infer tail (values++[p])) end.
(* A trace consists exclusively of executions of the actual generated
   interner. It can be consumed by proofs of generated straight-line builders. *)
Inductive executes observations : list operation -> Machine -> list Z -> Machine -> list Z -> Prop :=
| finished s ids : executes observations [] s ids s ids
| emitted op tail s ids middle id final result :
    execObserved (funcdef_0__intern (fun _=>false) (parameters ids op)) (s,observations) = Some (tt,(middle,observations)) ->
    meta_value middle 0 = id -> (0 < length (memory middle arraydef_0__meta))%nat -> executes observations tail middle (ids++[id]) final result ->
    executes observations (op::tail) s ids final result.
Theorem complete plan s fs ids values result reserve observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 -> represents fs ids values ->
  Forall fits plan -> infer plan values = Some result ->
  Z.of_nat (length fs + length plan + reserve) <= 9223372036854775807 ->
  exists final next result_ids, executes observations plan s ids final result_ids /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\ meta_value final 8 = 0 /\
    represents next result_ids result /\ (exists extra,next=fs++extra) /\
    Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  induction plan as [|op tail IH] in s,fs,ids,values |- *.
  - intros Harena Herror Hrep Hfits Hinfer Hbudget. injection Hinfer as <-.
    exists s,fs,ids. split; [constructor|]. split; [apply InternExecution.logical_refl|]. split; [exact Harena|]. split; [exact Herror|]. split; [exact Hrep|]. split; [exists []; now rewrite app_nil_r|]. cbn [length] in Hbudget. now rewrite Nat.add_0_r in Hbudget.
  - intros Harena Herror Hrep Hfits Hinfer Hbudget. inversion Hfits as [|head rest Hop Htail]; subst head rest.
    cbn [infer] in Hinfer. destruct (meaning values op) as [p|] eqn:Hp; [|discriminate].
    assert (Hstepbudget : Z.of_nat (length fs + S (length tail + reserve)) <= 9223372036854775807)
      by (replace (length fs + S (length tail + reserve))%nat with (length fs + length (op::tail) + reserve)%nat by (cbn; lia); exact Hbudget).
    destruct (step s fs ids values op p (length tail+reserve) observations Harena Herror Hrep Hop Hp Hstepbudget)
      as [middle [middle_fs [index [Hrun [Hframe [Hmiddle [Hflag [Hindex [Hmiddle_rep [Hprefix Hremaining]]]]]]]]]].
    replace (length middle_fs + (length tail + reserve))%nat with (length middle_fs + length tail + reserve)%nat in Hremaining by lia.
    destruct (IH middle middle_fs (ids++[Z.of_nat index]) (values++[p]) Hmiddle Hflag Hmiddle_rep Htail Hinfer Hremaining)
      as [final [next [result_ids [Htrace [Hlast_frame [Hlast [Hlast_flag [Hlast_rep [Hlast_prefix Hlast_reserve]]]]]]]]].
    exists final,next,result_ids. split.
    + econstructor; [exact Hrun|exact Hindex| |exact Htrace]. pose proof (proj1 (proj1 Hmiddle)) as [Hmeta Hrest]. lia.
    + split.
      * exact (InternExecution.logical_trans s middle final Hframe Hlast_frame).
      * split; [exact Hlast|]. split; [exact Hlast_flag|]. split; [exact Hlast_rep|]. split; [eapply InternReserve.extends_trans; eassumption|exact Hlast_reserve].
Qed.
End FormulaCircuit.
