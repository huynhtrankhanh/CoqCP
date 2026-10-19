From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module SipHashExecution.
Import IndexExecution.
Definition lanes := (Z * Z * Z * Z)%type.
Definition rotate x n := Z.lor
  (Z.land (Z.shiftl x n) (Z.ones 64))
  (Z.land (Z.shiftr x (64-n)) (Z.ones 64)).
Definition sip_round (v : lanes) : lanes :=
  let '(a,b,c,d) := v in
  let a := coerceInt (a+b) 64 in
  let b := Z.lxor (rotate b 13) a in
  let a := rotate a 32 in
  let c := coerceInt (c+d) 64 in
  let d := Z.lxor (rotate d 16) c in
  let a := coerceInt (a+d) 64 in
  let d := Z.lxor (rotate d 21) a in
  let c := coerceInt (c+b) 64 in
  let b := Z.lxor (rotate b 17) c in
  let c := rotate c 32 in (a,b,c,d).
Definition read_lanes (s : Machine) : lanes :=
  List.nth 0 (memory s arraydef_0__sipState) (0,0,0,0).
Definition put_lanes (s : Machine) (v : lanes) :=
  withMemory s (modifyArray (memory s) arraydef_0__sipState 0 v).

Lemma put_lanes_read s v : (0 < length (memory s arraydef_0__sipState))%nat ->
  read_lanes (put_lanes s v) = v.
Proof. intro H. unfold read_lanes, put_lanes. cbn [withMemory memory].
  change (List.nth 0 (<[0%nat := v]> (memory s arraydef_0__sipState)) (0,0,0,0) = v).
  destruct (memory s arraydef_0__sipState); [cbn in H; lia |reflexivity]. Qed.
Lemma put_lanes_length s v :
  length (memory (put_lanes s v) arraydef_0__sipState) =
  length (memory s arraydef_0__sipState).
Proof. unfold put_lanes. cbn [withMemory memory].
  change (length (<[0%nat := v]> (memory s arraydef_0__sipState)) =
    length (memory s arraydef_0__sipState)).
  apply length_insert. Qed.
Lemma put_lanes_other s v name : name <> arraydef_0__sipState ->
  memory (put_lanes s v) name = memory s name.
Proof. destruct name; intro H; try congruence; reflexivity. Qed.
Theorem generated_round s bs ns :
  (0 < length (memory s arraydef_0__sipState))%nat ->
  exec (funcdef_0__sipRound bs ns) s =
    Some (tt, put_lanes s (sip_round (read_lanes s))).
Proof.
  intro Hlength.
  unfold funcdef_0__sipRound. rewrite exec_eliminate. unfold funcdef_0__sipRound_body.
  cbv beta iota zeta delta [numberLocalGet numberLocalSet retrieve store addInt xorBits orBits
    shiftLeft shiftRight bind execLocal localStep step optionBind nums bools
    setNum setMachine machine fst snd Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__sipRound varsfuncdef_0__sipRound_rec].
  repeat first [rewrite nth_lt_default with (default := (0,0,0,0))
    | rewrite bool_decide_true by lia | rewrite bool_decide_false by lia
    | progress cbv beta iota zeta delta [bind execLocal localStep step optionBind nums bools
        setNum setMachine machine fst snd Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__sipRound varsfuncdef_0__sipRound_rec]
    | match goal with |- context [Z.ge_dec ?a ?b] =>
        destruct (Z.ge_dec a b); [exfalso; lia|] end
    | match goal with |- context [Nat.lt_dec ?i ?n] =>
        destruct (Nat.lt_dec i n); [|exfalso; lia] end
    | case_decide; [|lia]].
  unfold put_lanes, sip_round, read_lanes, rotate.
  replace (Z.to_nat 0) with 0%nat by reflexivity.
  lazymatch goal with |- context [@List.nth ?T 0 ?xs ?zero] =>
    destruct (@List.nth T 0 xs zero) as [[[a b] c] d] eqn:Hv
  end.
  change (read_lanes s = (a,b,c,d)) in Hv. unfold read_lanes in Hv.
  rewrite Hv. reflexivity.
Qed.

Definition xor_first (v : lanes) w := let '(a,b,c,d) := v in (Z.lxor a w,b,c,d).
Definition xor_last (v : lanes) w := let '(a,b,c,d) := v in (a,b,c,Z.lxor d w).
Lemma xor_first_components v w : xor_first v w =
  (Z.lxor (fst (fst (fst v))) w, snd (fst (fst v)), snd (fst v), snd v).
Proof. destruct v as [[[a b] c] d]. reflexivity. Qed.
Lemma xor_last_components v w : xor_last v w =
  (fst (fst (fst v)), snd (fst (fst v)), snd (fst v), Z.lxor (snd v) w).
Proof. destruct v as [[[a b] c] d]. reflexivity. Qed.
Definition round_state (s : Machine) := put_lanes s (sip_round (read_lanes s)).
Definition word_state (s : Machine) w :=
  let first := put_lanes s (xor_last (read_lanes s) w) in
  let second := round_state (round_state first) in
  put_lanes second (xor_first (read_lanes second) w).
Definition sip_word v w := xor_first (sip_round (sip_round (xor_last v w))) w.

Lemma local_read_lanes {V} `{EqDecision V} (f : @Execution.Frame arrayIndex1
    (arrayType _ environment1) V) :
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__sipState 0) f = Some (read_lanes (machine f),f).
Proof.
  destruct f as [s bs ns]. intro Hlength.
  cbn [retrieve execLocal localStep step]. case_decide; [|lia].
  rewrite nth_lt_default with (default := (0,0,0,0)). reflexivity.
Qed.
Lemma local_put_lanes {V} `{EqDecision V} (f : @Execution.Frame arrayIndex1
    (arrayType _ environment1) V) v :
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  execLocal (R := unit) (store _ _ _ arraydef_0__sipState 0 v) f =
    Some (tt, setMachine f (put_lanes (machine f) v)).
Proof.
  intro Hlength. cbn [store execLocal localStep step]. case_decide; [reflexivity|lia].
Qed.

Ltac sip_length :=
  cbn [machine setMachine];
  repeat rewrite put_lanes_length; try assumption.

Theorem generated_word s bs ns :
  (0 < length (memory s arraydef_0__sipState))%nat ->
  exec (funcdef_0__sipWord bs ns) s =
    Some (tt, word_state s (ns vardef_0__sipWord_word)).
Proof.
  intro Hlength. unfold funcdef_0__sipWord. rewrite exec_eliminate.
  unfold funcdef_0__sipWord_body.
  repeat first [rewrite execLocal_bind
    |rewrite execLocal_lift
    |rewrite generated_round by sip_length
    |rewrite local_read_lanes by sip_length
    |rewrite local_put_lanes by sip_length
    |progress cbn [bind execLocal optionBind numberLocalGet localStep nums bools machine
      setMachine fst snd xorBits]
  ].
  unfold word_state, round_state.
  rewrite xor_first_components, xor_last_components. reflexivity.
Qed.

Lemma round_state_length s :
  length (memory (round_state s) arraydef_0__sipState) =
  length (memory s arraydef_0__sipState).
Proof. apply put_lanes_length. Qed.
Lemma word_state_length s w :
  length (memory (word_state s w) arraydef_0__sipState) =
  length (memory s arraydef_0__sipState).
Proof. unfold word_state. rewrite put_lanes_length, !round_state_length, put_lanes_length. reflexivity. Qed.
Lemma round_state_other s name : name <> arraydef_0__sipState ->
  memory (round_state s) name = memory s name.
Proof. apply put_lanes_other. Qed.
Lemma word_state_other s w name : name <> arraydef_0__sipState ->
  memory (word_state s w) name = memory s name.
Proof. intro H. unfold word_state, round_state. now repeat rewrite put_lanes_other by exact H. Qed.
Lemma word_state_value s w : (0 < length (memory s arraydef_0__sipState))%nat ->
  read_lanes (word_state s w) = sip_word (read_lanes s) w.
Proof.
  intro H. unfold word_state, round_state, sip_word.
  repeat rewrite put_lanes_read by (repeat rewrite put_lanes_length; exact H).
  reflexivity.
Qed.

Definition meta_value (s : Machine) slot := List.nth slot (memory s arraydef_0__meta) 0.
Definition initialize k0 k1 : lanes :=
  (Z.lxor 8317987319222330741 k0, Z.lxor 7237128888997146477 k1,
   Z.lxor 7816392313619706465 k0, Z.lxor 8387220255154660723 k1).
Definition finalize (v : lanes) := let '(a,b,c,d) := v in (a,b,Z.lxor c 255,d).
Definition digest (v : lanes) := Z.lxor (Z.lxor (Z.lxor (fst (fst (fst v)))
  (snd (fst (fst v)))) (snd (fst v))) (snd v).
Definition hash_work_state s tag a b :=
  let seeded := put_lanes s (initialize (meta_value s 26) (meta_value s 27)) in
  let compressed := word_state (word_state (word_state (word_state seeded tag) a) b) 1729382256910270464 in
  let marked := put_lanes compressed (finalize (read_lanes compressed)) in
  round_state (round_state (round_state (round_state marked))).
Definition hash_state s tag a b :=
  let worked := hash_work_state s tag a b in
  let value := digest (read_lanes worked) in
  let saved := store_meta worked 28 value in
  store_meta saved 21 (value mod meta_value saved 20).
Definition siphash24 k0 k1 tag a b :=
  let compressed := sip_word (sip_word (sip_word (sip_word (initialize k0 k1) tag) a) b) 1729382256910270464 in
  digest (sip_round (sip_round (sip_round (sip_round (finalize compressed))))).
Lemma finalize_components v : finalize v =
  (fst (fst (fst v)), snd (fst (fst v)), Z.lxor (snd (fst v)) 255, snd v).
Proof. destruct v as [[[a b] c] d]. reflexivity. Qed.

Lemma local_read_meta {V} `{EqDecision V} (f : @Execution.Frame arrayIndex1
    (arrayType _ environment1) V) slot :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal (R := Z) (retrieve _ _ _ arraydef_0__meta slot) f =
    Some (meta_value (machine f) (Z.to_nat slot),f).
Proof.
  destruct f as [s bs ns]. intro Hlength.
  cbn [retrieve execLocal localStep step]. case_decide; [|lia].
  rewrite nth_lt_default with (default := 0). reflexivity.
Qed.
Lemma local_put_meta {V} `{EqDecision V} (f : @Execution.Frame arrayIndex1
    (arrayType _ environment1) V) slot v :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal (R := unit) (store _ _ _ arraydef_0__meta slot v) f =
    Some (tt, setMachine f (store_meta (machine f) (Z.to_nat slot) v)).
Proof.
  intro Hlength. cbn [store execLocal localStep step].
  case_decide; [reflexivity|lia].
Qed.

(* Prove loop translation at execution level, without the extensionality
   assumptions of the corresponding equality between free-monad programs. *)
Lemma exec_drop_lift {V} `{EqDecision V} {R}
  (code : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V)
    withLocalVariablesReturnValue R) next f :
  execLocal (dropWithinLoop (liftToWithinLoop code >>= next)) f =
  optionBind (execLocal code f) (fun response =>
    execLocal (dropWithinLoop (next (fst response))) (snd response)).
Proof.
  induction code as [value|effect cont IH] in f |- *; [reflexivity|].
  cbn [liftToWithinLoop Action_rect bind dropWithinLoop execLocal].
  destruct (localStep effect f) as [[value after]|]; [|reflexivity].
  cbn [optionBind fst snd]. apply IH.
Qed.

Lemma meta_put_lanes s v i : meta_value (put_lanes s v) i = meta_value s i.
Proof. unfold meta_value. now rewrite put_lanes_other by discriminate. Qed.
Lemma meta_word s w i : meta_value (word_state s w) i = meta_value s i.
Proof. unfold meta_value. now rewrite word_state_other by discriminate. Qed.
Lemma meta_round s i : meta_value (round_state s) i = meta_value s i.
Proof. apply meta_put_lanes. Qed.
Lemma meta_store_other s i j v : i <> j ->
  meta_value (store_meta s j v) i = meta_value s i.
Proof.
  intro H. unfold meta_value, store_meta. cbn [withMemory memory].
  rewrite modify_meta. now apply ArrayFacts.nth_insert_other.
Qed.

Ltac hash_lengths := cbn [machine setMachine setNum];
  repeat first [rewrite put_lanes_length |rewrite round_state_length |rewrite word_state_length
    |rewrite put_lanes_other by discriminate |rewrite word_state_other by discriminate
    |rewrite round_state_other by discriminate
    |rewrite store_meta_length]; try assumption; try lia.

Ltac fold_round_state := match goal with
  |- context [put_lanes ?s (sip_round (read_lanes ?s))] => progress fold (round_state s)
  end.

Lemma hash_work_other s tag a b name : name <> arraydef_0__sipState ->
  memory (hash_work_state s tag a b) name = memory s name.
Proof.
  intro H. unfold hash_work_state, round_state.
  now repeat first [rewrite put_lanes_other by exact H |rewrite word_state_other by exact H].
Qed.
Lemma meta_hash_work s tag a b i : meta_value (hash_work_state s tag a b) i = meta_value s i.
Proof. unfold meta_value. now rewrite hash_work_other by discriminate. Qed.

Lemma generated_round_state s bs ns :
  (0 < length (memory s arraydef_0__sipState))%nat ->
  exec (funcdef_0__sipRound bs ns) s = Some (tt, round_state s).
Proof. apply generated_round. Qed.

(* Callers use the proved interfaces instead of expanding twelve rounds into
   every execution context during conversion. *)
Local Opaque funcdef_0__sipRound funcdef_0__sipWord round_state word_state put_lanes read_lanes sip_round.

Definition word_function := (varsfuncdef_0__sipWord -> bool) ->
  (varsfuncdef_0__sipWord -> Z) -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition round_function := (varsfuncdef_0__sipRound -> bool) ->
  (varsfuncdef_0__sipRound -> Z) -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition hash_body (word_proc : word_function) (round_proc : round_function) :
  Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval unfold funcdef_0__formulaHash_body in funcdef_0__formulaHash_body in
  let generalized := eval pattern funcdef_0__sipWord, funcdef_0__sipRound in code in
  lazymatch generalized with ?family _ _ => exact (family word_proc round_proc) end).
Definition work_model (w : Machine -> Z -> Machine) (r : Machine -> Machine) := ltac:(
  let code := eval unfold hash_work_state in hash_work_state in
  let generalized := eval pattern word_state, round_state in code in
  lazymatch generalized with ?family _ _ => exact (family w r) end).
Definition state_model w r s tag a b :=
  let worked := work_model w r s tag a b in
  let value := digest (read_lanes worked) in
  let saved := store_meta worked 28 value in
  store_meta saved 21 (value mod meta_value saved 20).

Section HashComposition.
Variable word_proc : word_function.
Variable round_proc : round_function.
Variable w_state : Machine -> Z -> Machine.
Variable r_state : Machine -> Machine.
Hypothesis w_length : forall s w,
  length (memory (w_state s w) arraydef_0__sipState) = length (memory s arraydef_0__sipState).
Hypothesis r_length : forall s,
  length (memory (r_state s) arraydef_0__sipState) = length (memory s arraydef_0__sipState).
Hypothesis w_other : forall s w name, name <> arraydef_0__sipState ->
  memory (w_state s w) name = memory s name.
Hypothesis r_other : forall s name, name <> arraydef_0__sipState ->
  memory (r_state s) name = memory s name.
Lemma w_meta s w i : meta_value (w_state s w) i = meta_value s i.
Proof. unfold meta_value. now rewrite w_other by discriminate. Qed.
Lemma r_meta s i : meta_value (r_state s) i = meta_value s i.
Proof. unfold meta_value. now rewrite r_other by discriminate. Qed.
Lemma work_meta s tag a b i : meta_value (work_model w_state r_state s tag a b) i = meta_value s i.
Proof. unfold work_model. now repeat first
  [rewrite r_meta |rewrite w_meta |rewrite meta_put_lanes]. Qed.
Ltac composition_lengths := cbn [machine setMachine setNum];
  repeat first [rewrite put_lanes_length |rewrite w_length |rewrite r_length
    |rewrite put_lanes_other by discriminate |rewrite w_other by discriminate
    |rewrite r_other by discriminate |rewrite store_meta_length]; try assumption; try lia.
Hypothesis word_correct : forall s bs ns,
  (0 < length (memory s arraydef_0__sipState))%nat ->
  exec (word_proc bs ns) s = Some (tt,w_state s (ns vardef_0__sipWord_word)).
Hypothesis round_correct : forall s bs ns,
  (0 < length (memory s arraydef_0__sipState))%nat ->
  exec (round_proc bs ns) s = Some (tt,r_state s).

Theorem hash_composition s bs ns :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  0 < meta_value s 20 ->
  exec (eliminateLocalVariables bs ns (hash_body word_proc round_proc)) s =
    Some (tt, state_model w_state r_state s (ns vardef_0__formulaHash_tag)
      (ns vardef_0__formulaHash_a) (ns vardef_0__formulaHash_b)).
Proof.
  intros Hmeta Hsip Hpositive.
  change (0 < meta_value s (Z.to_nat 20)) in Hpositive.
  rewrite exec_eliminate. unfold hash_body.
  repeat first [progress replace (Z.to_nat 4) with 4%nat by reflexivity
    |rewrite execLocal_bind
    |rewrite dropWithinLoop_1
    |rewrite exec_drop_lift
    |rewrite execLocal_lift
    |rewrite word_correct by composition_lengths
    |rewrite round_correct by composition_lengths
    |rewrite local_read_lanes by composition_lengths
    |rewrite local_put_lanes by composition_lengths
    |rewrite local_read_meta by composition_lengths
    |rewrite local_put_meta by composition_lengths
    |rewrite meta_put_lanes |rewrite w_meta |rewrite r_meta
    |rewrite meta_store_other by lia
    |rewrite decide_False by lia
    |progress cbn [bind execLocal optionBind numberLocalGet numberLocalSet localStep nums bools machine
      setNum setMachine fst snd xorBits modIntUnsigned loop Z.to_nat dropWithinLoop_1
      Imperative.update variableIndexEqualityDecidablevarsfuncdef_0__formulaHash
      varsfuncdef_0__formulaHash_rec]
  ].
  lazymatch goal with |- Some _ = Some _ => idtac | _ => fail "unfinished symbolic execution" end.
  unfold state_model. rewrite meta_store_other by lia. rewrite work_meta.
  unfold work_model, initialize, digest.
  rewrite finalize_components. reflexivity.
Qed.

End HashComposition.

Theorem generated_hash s bs ns :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  0 < meta_value s 20 ->
  exec (funcdef_0__formulaHash bs ns) s =
    Some (tt, hash_state s (ns vardef_0__formulaHash_tag)
      (ns vardef_0__formulaHash_a) (ns vardef_0__formulaHash_b)).
Proof.
  exact (hash_composition funcdef_0__sipWord funcdef_0__sipRound word_state round_state
    word_state_length round_state_length word_state_other round_state_other
    generated_word generated_round_state s bs ns).
Qed.

Local Transparent funcdef_0__sipRound funcdef_0__sipWord round_state word_state put_lanes read_lanes sip_round.

Lemma meta_store_same s i v : (i < length (memory s arraydef_0__meta))%nat ->
  meta_value (store_meta s i v) i = v.
Proof.
  intro H. unfold meta_value, store_meta. cbn [withMemory memory].
  rewrite modify_meta. now apply OverflowExecution.nth_insert_same.
Qed.
Lemma hash_work_length s tag a b :
  length (memory (hash_work_state s tag a b) arraydef_0__sipState) =
  length (memory s arraydef_0__sipState).
Proof. unfold hash_work_state. now repeat first
  [rewrite round_state_length |rewrite word_state_length |rewrite put_lanes_length]. Qed.
Lemma round_state_value s : (0 < length (memory s arraydef_0__sipState))%nat ->
  read_lanes (round_state s) = sip_round (read_lanes s).
Proof. apply put_lanes_read. Qed.
Lemma hash_work_value s tag a b : (0 < length (memory s arraydef_0__sipState))%nat ->
  digest (read_lanes (hash_work_state s tag a b)) =
    siphash24 (meta_value s 26) (meta_value s 27) tag a b.
Proof.
  intro H. unfold hash_work_state, siphash24.
  repeat first [rewrite round_state_value by hash_lengths
    |rewrite word_state_value by hash_lengths |rewrite put_lanes_read by hash_lengths].
  reflexivity.
Qed.
Lemma hash_result s tag a b :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  meta_value (hash_state s tag a b) 28 =
    siphash24 (meta_value s 26) (meta_value s 27) tag a b.
Proof.
  intros Hmeta Hsip. unfold hash_state.
  rewrite meta_store_other by lia.
  rewrite meta_store_same.
  - now apply hash_work_value.
  - rewrite hash_work_other by discriminate. exact Hmeta.
Qed.
Lemma hash_bucket s tag a b :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  meta_value (hash_state s tag a b) 21 =
    siphash24 (meta_value s 26) (meta_value s 27) tag a b mod meta_value s 20.
Proof.
  intros Hmeta Hsip. unfold hash_state. rewrite meta_store_same.
  - rewrite meta_store_other by lia. rewrite meta_hash_work.
    rewrite hash_work_value by exact Hsip. reflexivity.
  - rewrite store_meta_length, hash_work_other by discriminate. lia.
Qed.
Lemma hash_preserves_array s tag a b name : name <> arraydef_0__meta ->
  name <> arraydef_0__sipState -> memory (hash_state s tag a b) name = memory s name.
Proof.
  intros Hmeta Hsip. unfold hash_state.
  rewrite !store_meta_other by exact Hmeta. now apply hash_work_other.
Qed.
Lemma hash_preserves_meta s tag a b i : i <> 21%nat -> i <> 28%nat ->
  meta_value (hash_state s tag a b) i = meta_value s i.
Proof.
  intros H21 H28. unfold hash_state. rewrite !meta_store_other by assumption.
  unfold meta_value. now rewrite hash_work_other by discriminate.
Qed.
Lemma hash_io s tag a b : stdin (hash_state s tag a b) = stdin s /\
  stdout (hash_state s tag a b) = stdout s.
Proof. split; reflexivity. Qed.

Theorem generated_hash_correct s bs ns :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> 0 < meta_value s 20 ->
  exists final,
    exec (funcdef_0__formulaHash bs ns) s = Some (tt,final) /\
    meta_value final 28 = siphash24 (meta_value s 26) (meta_value s 27)
      (ns vardef_0__formulaHash_tag) (ns vardef_0__formulaHash_a) (ns vardef_0__formulaHash_b) /\
    meta_value final 21 = meta_value final 28 mod meta_value s 20 /\
    0 <= meta_value final 21 < meta_value s 20 /\
    (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
      memory final name = memory s name) /\
    (forall i, i <> 21%nat -> i <> 28%nat -> meta_value final i = meta_value s i) /\
    stdin final = stdin s /\ stdout final = stdout s.
Proof.
  intros Hmeta Hsip Hpositive.
  exists (hash_state s (ns vardef_0__formulaHash_tag) (ns vardef_0__formulaHash_a)
    (ns vardef_0__formulaHash_b)).
  split; [now apply generated_hash|]. split; [now apply hash_result|].
  split; [rewrite hash_bucket, hash_result by assumption; reflexivity|].
  split; [rewrite hash_bucket by assumption; now apply Z.mod_pos_bound|].
  split; [intros; now apply hash_preserves_array|].
  split; [intros; now apply hash_preserves_meta|]. apply hash_io.
Qed.
End SipHashExecution.
