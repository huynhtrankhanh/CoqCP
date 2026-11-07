From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram UniformMemoChains.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

(* Isolate the actual loop generated for the unconnected memo implementation.
   These are local Action execution lemmas, not a full lookup refinement. *)
Module UniformMemoLoop.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformMemoGet)
  withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformMemoGet.
Definition scan_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformMemoGet_body in funcdef_0__uniformMemoGet_body in
  let code := eval cbn zeta in code in
  lazymatch code with context [loop _ ?body] =>
    let body := eval cbn zeta in body in exact body
  end).

Theorem scan_empty (f : Frame) remaining : nums f vardef_0__uniformMemoGet_current = 0 ->
  execLocal (scan_body remaining) f = Some (Stop,f).
Proof.
  destruct f as [s bs ns]. cbn [nums]. intro Hcurrent.
  unfold scan_body. cbn zeta.
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break
    execLocal localStep step optionBind fst snd nums machine setNum setMachine].
  rewrite Hcurrent, bool_decide_true by reflexivity. reflexivity.
Qed.

Definition maximum : Z := 18446744073709551615.
Definition word x := 0 <= x <= maximum.
Lemma coerce_word x : word x -> coerceInt x 64 = x.
Proof. intros H. unfold coerceInt. apply Z.mod_small. unfold word, maximum in H. lia. Qed.
Definition next_frame (f : Frame) index link :=
  setNum (setNum f vardef_0__uniformMemoGet_current (Z.of_nat index))
    vardef_0__uniformMemoGet_current link.

(* On a nonmatching entry, the generated loop advances to its stored link. *)
Theorem scan_mismatch (f : Frame) remaining index key depth value link :
  nums f vardef_0__uniformMemoGet_current = Z.of_nat (S index) ->
  Z.of_nat (S index) <= maximum ->
  (index < length (memory (machine f) arraydef_0__uniformMemoEntries))%nat ->
  List.nth index (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) = (key,depth,value,link) ->
  (key <> nums f vardef_0__uniformMemoGet_node \/ depth <> nums f vardef_0__uniformMemoGet_depth) ->
  execLocal (scan_body remaining) f = Some (KeepGoing,next_frame f index link).
Proof.
  intros Hcurrent Hlimit Hentries Hentry Hmismatch.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  change (@List.nth (Z*Z*Z*Z)%type index (memory s arraydef_0__uniformMemoEntries) (0,0,0,0) = (key,depth,value,link)) in Hentry.
  destruct (Z.eq_dec key (ns vardef_0__uniformMemoGet_node));
    destruct (Z.eq_dec depth (ns vardef_0__uniformMemoGet_depth)); try tauto.
  all: unfold scan_body; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformMemoGet varsfuncdef_0__uniformMemoGet_rec].
  all: repeat first [rewrite Hcurrent
    |rewrite (coerce_word (Z.of_nat (S index) - 1)) by (unfold word, maximum in *; lia)
    |progress replace (Z.of_nat (S index) - 1) with (Z.of_nat index) by lia
    |rewrite Nat2Z.id
    |rewrite nth_lt_default with (default := (0,0,0,0))
    |rewrite Hentry
    |match goal with |- context [bool_decide ?P] =>
        first [rewrite (bool_decide_true P) by congruence
          |rewrite (bool_decide_false P) by (first [congruence|lia])]
      end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
        shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
        execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
        Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__uniformMemoGet varsfuncdef_0__uniformMemoGet_rec next_frame]
    |match goal with |- context [Nat.lt_dec ?i ?n] =>
        destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |case_decide; [|lia]
  ].
  all: reflexivity.
Qed.

Definition hit_frame (f : Frame) index count value :=
  setMachine (setNum f vardef_0__uniformMemoGet_current (Z.of_nat index))
    (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoState 0
      (count, nums f vardef_0__uniformMemoGet_size, 1, value))).

(* A matching entry records its value and breaks immediately. *)
Theorem scan_hit (f : Frame) remaining index count size found oldvalue value link :
  nums f vardef_0__uniformMemoGet_current = Z.of_nat (S index) ->
  Z.of_nat (S index) <= maximum ->
  (index < length (memory (machine f) arraydef_0__uniformMemoEntries))%nat ->
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth index (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) =
    (nums f vardef_0__uniformMemoGet_node, nums f vardef_0__uniformMemoGet_depth,value,link) ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,found,oldvalue) ->
  execLocal (scan_body remaining) f = Some (Stop,hit_frame f index count value).
Proof.
  intros Hcurrent Hlimit Hentries Hstate Hentry Hstatevalue.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  change (@List.nth (Z*Z*Z*Z)%type index (memory s arraydef_0__uniformMemoEntries) (0,0,0,0) =
    (ns vardef_0__uniformMemoGet_node,ns vardef_0__uniformMemoGet_depth,value,link)) in Hentry.
  change (@List.nth (Z*Z*Z*Z)%type 0 (memory s arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,found,oldvalue)) in Hstatevalue.
  unfold scan_body. cbn zeta.
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformMemoGet varsfuncdef_0__uniformMemoGet_rec].
  repeat first [rewrite Hcurrent
    |rewrite (coerce_word (Z.of_nat (S index) - 1)) by (unfold word, maximum in *; lia)
    |progress replace (Z.to_nat 0) with O by reflexivity
    |progress replace (Z.of_nat (S index) - 1) with (Z.of_nat index) by lia
    |rewrite Nat2Z.id
    |rewrite nth_lt_default with (default := (0,0,0,0))
    |rewrite Hentry |rewrite Hstatevalue
    |match goal with |- context [bool_decide ?P] =>
        first [rewrite (bool_decide_true P) by congruence
          |rewrite (bool_decide_false P) by (first [congruence|lia])]
      end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
        shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
        execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
        Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__uniformMemoGet varsfuncdef_0__uniformMemoGet_rec hit_frame]
    |match goal with |- context [Nat.lt_dec ?i ?n] =>
        destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |case_decide; [|lia]
  ].
  reflexivity.
Qed.

Definition entries_valid (f : Frame) count :=
  (count <= length (memory (machine f) arraydef_0__uniformMemoEntries))%nat /\
  forall i, (i < count)%nat ->
    let '(_,_,_,link) := List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) in
    0 <= link <= Z.of_nat count.

Fixpoint scan_values (f : Frame) fuel pointer : option Z :=
  match fuel,pointer with
  | O,_ | _,O => None
  | S fuel', S i =>
    let '(key,depth,value,link) := List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) in
    if bool_decide (key = nums f vardef_0__uniformMemoGet_node /\ depth = nums f vardef_0__uniformMemoGet_depth)
    then Some value else scan_values f fuel' (Z.to_nat link)
  end.

Definition observed_result (f : Frame) : option Z :=
  let '(_,_,found,value) := List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) in
  if bool_decide (found = 1) then Some value else None.

Lemma next_observed f i link : observed_result (next_frame f i link) = observed_result f.
Proof. destruct f. reflexivity. Qed.
Lemma next_scan f i link fuel pointer : scan_values (next_frame f i link) fuel pointer = scan_values f fuel pointer.
Proof.
  induction fuel as [|fuel IH] in pointer |- *; [reflexivity|]. destruct pointer as [|pointer]; [reflexivity|].
  destruct f as [s bs ns]. cbn [scan_values next_frame machine nums setNum].
  destruct (List.nth pointer (memory s arraydef_0__uniformMemoEntries) (0,0,0,0)) as [[[key depth] value] next].
  cbv beta iota zeta delta [Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformMemoGet varsfuncdef_0__uniformMemoGet_rec].
  destruct (bool_decide (key = ns vardef_0__uniformMemoGet_node /\ depth = ns vardef_0__uniformMemoGet_depth)); [reflexivity|].
  apply IH.
Qed.
Lemma hit_observed f i count size found oldvalue value :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,found,oldvalue) ->
  observed_result (hit_frame f i count value) = Some value.
Proof.
  destruct f as [s bs ns]. cbn [machine nums]. intros Hlen Hstate.
  unfold observed_result, hit_frame. cbn [machine setMachine setNum withMemory memory].
  change ((let '(_,_,found,value) := List.nth 0 (<[0%nat := (count,ns vardef_0__uniformMemoGet_size,1,value)]> (memory s arraydef_0__uniformMemoState)) (0,0,0,0) in
          if bool_decide (found = 1) then Some value else None) = Some value).
  destruct (memory s arraydef_0__uniformMemoState); [cbn in Hlen; lia|].
  cbn. rewrite bool_decide_true by reflexivity. reflexivity.
Qed.

(* Arbitrary fuel and collision chains: the actual generated loop agrees with
   an independent scan of the entry array. The hashing prelude is not covered. *)
Theorem scan_loop_refines fuel (f : Frame) count pointer :
  entries_valid f count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  nums f vardef_0__uniformMemoGet_current = Z.of_nat pointer -> (pointer <= count)%nat ->
  observed_result f = None ->
  exists final, execLocal (loop fuel scan_body) f = Some (tt,final) /\
    observed_result final = scan_values f fuel pointer.
Proof.
  induction fuel as [|fuel IH] in f, pointer |- *.
  - intros Hvalid Hlimit Hstate Hpointer Hbound Hinitial. exists f. cbn [loop scan_values]. auto.
  - intros [Hentries Hlinks] Hlimit Hstate Hpointer Hbound Hinitial.
    rewrite loop_S, execLocal_bind.
    destruct pointer as [|i].
    + rewrite scan_empty by exact Hpointer. cbn [optionBind fst snd scan_values]. exists f. auto.
    + destruct (List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0)) as [[[key depth] value] link] eqn:Hentry.
      destruct (List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0)) as [[[count0 size0] found] oldvalue] eqn:Hstatevalue.
      destruct (decide (key = nums f vardef_0__uniformMemoGet_node /\ depth = nums f vardef_0__uniformMemoGet_depth)) as [[Hkey Hdepth]|Hneq].
      * subst key depth. rewrite (scan_hit f fuel i count0 size0 found oldvalue value link) by (try assumption; lia).
        cbn [optionBind fst snd scan_values]. rewrite Hentry, bool_decide_true by tauto.
        exists (hit_frame f i count0 value). split; [reflexivity|]. eapply hit_observed; eassumption.
      * assert (Hmismatch : key <> nums f vardef_0__uniformMemoGet_node \/ depth <> nums f vardef_0__uniformMemoGet_depth).
        { destruct (Z.eq_dec key (nums f vardef_0__uniformMemoGet_node)) as [Hk|Hk]; [right; intro Hd; apply Hneq; auto|left; exact Hk]. }
        rewrite (scan_mismatch f fuel i key depth value link) by (try assumption; lia).
        cbn [optionBind fst snd scan_values]. rewrite Hentry, bool_decide_false by exact Hneq.
        assert (Hlink : 0 <= link <= Z.of_nat count) by (specialize (Hlinks i ltac:(lia)); now rewrite Hentry in Hlinks).
        destruct (IH (next_frame f i link) (Z.to_nat link)) as [final [Hrun Hresult]].
        -- split; [exact Hentries|exact Hlinks].
        -- exact Hlimit.
        -- exact Hstate.
        -- change (link = Z.of_nat (Z.to_nat link)). rewrite Z2Nat.id by lia. reflexivity.
        -- pose proof (Z2Nat.id link ltac:(lia)). lia.
        -- now rewrite next_observed.
        -- exists final. split; [exact Hrun|]. now rewrite next_scan in Hresult.
Qed.

Definition natural_table (f : Frame) (i : nat) : UniformMemoChains.entry :=
  let '(key,depth,value,link) := List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) in
  UniformMemoChains.Entry (Z.to_nat key) (Z.to_nat depth) (Z.to_nat value) (Z.to_nat link).
Definition nonnegative_entries (f : Frame) count :=
  forall i, (i < count)%nat ->
    let '(key,depth,value,_) := List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0) in
    0 <= key /\ 0 <= depth /\ 0 <= value.

(* Bridge the concrete word-array scan to the separately verified natural
   collision-chain model. No assumption about hashing or bucket placement. *)
Theorem scan_values_natural fuel (f : Frame) count pointer key depth :
  entries_valid f count -> nonnegative_entries f count -> (pointer <= count)%nat ->
  nums f vardef_0__uniformMemoGet_node = Z.of_nat key ->
  nums f vardef_0__uniformMemoGet_depth = Z.of_nat depth ->
  scan_values f fuel pointer = option_map Z.of_nat (UniformMemoChains.scan (natural_table f) fuel pointer key depth).
Proof.
  induction fuel as [|fuel IH] in pointer |- *; [reflexivity|].
  destruct pointer as [|i]; [reflexivity|].
  intros [Hentries Hlinks] Hnonneg Hbound Hkey Hdepth.
  pose proof (Hnonneg i ltac:(lia)) as Hvals. pose proof (Hlinks i ltac:(lia)) as Hlink.
  cbn [scan_values UniformMemoChains.scan natural_table].
  destruct (List.nth i (memory (machine f) arraydef_0__uniformMemoEntries) (0,0,0,0)) as [[[k d] v] link] eqn:Hentry.
  cbn in Hvals,Hlink |- *. destruct Hvals as [Hk [Hd Hv]].
  unfold UniformMemoChains.matches.
  assert (Htable : natural_table f i = UniformMemoChains.Entry (Z.to_nat k) (Z.to_nat d) (Z.to_nat v) (Z.to_nat link)).
  { unfold natural_table. now rewrite Hentry. }
  rewrite Htable. cbn [UniformMemoChains.node UniformMemoChains.depth UniformMemoChains.value UniformMemoChains.next].
  case_bool_decide as Hmatch.
  - destruct Hmatch as [Hkm Hdm].
    assert (Hkm' : k = Z.of_nat key) by exact (eq_trans Hkm Hkey).
    assert (Hdm' : d = Z.of_nat depth) by exact (eq_trans Hdm Hdepth).
    rewrite Hkm', Hdm', !Nat2Z.id, !Nat.eqb_refl. cbn.
    now rewrite Z2Nat.id by lia.
  - assert (Hneq : ~ (k = Z.of_nat key /\ d = Z.of_nat depth)).
    { intros [H1 H2]. apply Hmatch. split; [exact (eq_trans H1 (eq_sym Hkey))|exact (eq_trans H2 (eq_sym Hdepth))]. }
    assert (Hnat : (Z.to_nat k =? key)%nat && (Z.to_nat d =? depth)%nat = false).
    { destruct ((Z.to_nat k =? key)%nat && (Z.to_nat d =? depth)%nat) eqn:Hnatmatch; [|reflexivity].
      apply andb_true_iff in Hnatmatch as [Hmk Hmd]. apply Nat.eqb_eq in Hmk. apply Nat.eqb_eq in Hmd.
      exfalso. apply Hneq. split; [rewrite <- Hmk, Z2Nat.id by lia|rewrite <- Hmd, Z2Nat.id by lia]; reflexivity. }
    rewrite Hnat. apply IH; try assumption.
    + split; assumption.
    + pose proof (Z2Nat.id link ltac:(lia)). lia.
Qed.
End UniformMemoLoop.
