From CoqCP Require Import Options Imperative Execution InteractiveExecution ArrayExecution DecimalEncoding.
From Submission Require Import KthHighestScore KthHighestScoreCode KthHighestScoreIO KthHighestScorePrinter KthHighestScoreProgram KthHighestScoreObservations.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Logic.FunctionalExtensionality.
Open Scope Z_scope.

Definition wireCountry c := match c with Finland => ProtocolFinland | Sweden => ProtocolSweden end.
Definition countryByte c : Z := match c with Finland => 70 | Sweden => 83 end.
Definition wireQueries qs := map (fun q : Query => (wireCountry (fst q), snd q)) qs.
Definition scoreArrays iv rv buffer : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__input => [iv] | arraydef_0__reply => [rv] | arraydef_0__printBuffer => buffer end.
Definition scoreState iv rv buffer input output : @Machine arrayIndex2 (arrayType _ environment2) :=
  {| memory := scoreArrays iv rv buffer; stdin := input; stdout := output |}.
Lemma modify_score_input iv rv buffer value :
  modifyArray (scoreArrays iv rv buffer) arraydef_0__input 0 value = scoreArrays value rv buffer.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma modify_score_reply iv rv buffer value :
  modifyArray (scoreArrays iv rv buffer) arraydef_0__reply 0 value = scoreArrays iv value buffer.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma reader_separator_observed value separator iv rv buffer tail prefix obs (hv : (value < 2^64)%nat) (hsep : invalidDigit separator = true) :
  execObserved mappedReader (scoreState iv rv buffer (decimalBytes value ++ separator :: tail) prefix, obs) =
  Some (tt, (scoreState (Z.of_nat value) rv buffer tail prefix, obs)).
Proof.
  apply observed_plain; [apply reader_NoFlush |].
  change (exec mappedReader (withInput (scoreState iv rv buffer [] prefix) (decimalBytes value ++ separator :: tail)) =
    Some (tt, scoreState (Z.of_nat value) rv buffer tail prefix)).
  rewrite decimalReaderExecution; try assumption; try reflexivity; [| cbn [memory scoreState scoreArrays length]; lia].
  unfold withMemory. cbn [memory withInput stdin stdout scoreState]. rewrite modify_score_input. reflexivity.
Qed.
Lemma reader_observed value iv rv buffer tail prefix obs (hv : (value < 2^64)%nat) :
  execObserved mappedReader (scoreState iv rv buffer (decimalBytes value ++ 10 :: tail) prefix, obs) =
  Some (tt, (scoreState (Z.of_nat value) rv buffer tail prefix, obs)).
Proof. apply reader_separator_observed; [exact hv | reflexivity]. Qed.
Lemma header_observed value iv rv buffer tail prefix obs (hv : (value < 2^64)%nat) :
  execObserved mappedReader (scoreState iv rv buffer (decimalBytes value ++ 32 :: tail) prefix, obs) =
  Some (tt, (scoreState (Z.of_nat value) rv buffer tail prefix, obs)).
Proof. apply reader_separator_observed; [exact hv | reflexivity]. Qed.
Lemma printer_observed value iv rv buffer input prefix obs
  (hv : (value < 2^64)%nat) (hb : length buffer = 20%nat) :
  exists buffer', execObserved (mappedPrinter (Z.of_nat value))
    (scoreState iv rv buffer input prefix, obs) =
    Some (tt, (scoreState iv rv buffer' input (prefix ++ decimalBytes value), obs)) /\ length buffer' = 20%nat.
Proof.
  destruct (printerExecutionAny value (scoreState iv rv buffer input prefix) hv hb) as (buffer' & executed & bound).
  exists buffer'. split; [| exact bound]. apply observed_plain; [apply printer_NoFlush | exact executed].
Qed.
Lemma reply_observed iv rv buffer input prefix obs :
  execObserved (@readArray arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0)
    (scoreState iv rv buffer input prefix, obs) = Some (rv, (scoreState iv rv buffer input prefix, obs)).
Proof. reflexivity. Qed.
Lemma input_observed iv rv buffer input prefix obs :
  execObserved (@readArray arrayIndex2 (arrayType _ environment2) arraydef_0__input 0)
    (scoreState iv rv buffer input prefix, obs) = Some (iv, (scoreState iv rv buffer input prefix, obs)).
Proof. reflexivity. Qed.
Lemma store_reply_observed iv rv buffer input prefix obs value :
  execObserved (@writeArray arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0 value)
    (scoreState iv rv buffer input prefix, obs) = Some (tt, (scoreState iv value buffer input prefix, obs)).
Proof.
  apply observed_plain; [apply write_NoFlush |].
  rewrite (execWrite arraydef_0__reply 0%nat value) by (cbn [memory scoreState scoreArrays length]; lia).
  unfold withMemory. cbn [memory scoreState stdin stdout]. rewrite modify_score_reply. reflexivity.
Qed.
Fixpoint protocolFlushes qs F S prefix tail :=
  match qs with
  | [] => []
  | q :: rest => {| flushedOutput := prefix ++ expectedQueryLine q;
      unreadInput := expectedResponses (q :: rest) F S ++ tail |} ::
      protocolFlushes rest F S (prefix ++ expectedQueryLine q) tail
  end.
Lemma responses_app qs rest F S : expectedResponses (qs ++ rest) F S =
  expectedResponses qs F S ++ expectedResponses rest F S.
Proof. unfold expectedResponses. rewrite map_app, concat_app. reflexivity. Qed.
Lemma requests_app qs rest : expectedRequests (qs ++ rest) = expectedRequests qs ++ expectedRequests rest.
Proof. unfold expectedRequests. rewrite map_app, concat_app. reflexivity. Qed.
Lemma protocol_app qs rest F S prefix tail :
  protocolFlushes (qs ++ rest) F S prefix tail =
  protocolFlushes qs F S prefix (expectedResponses rest F S ++ tail) ++
  protocolFlushes rest F S (prefix ++ expectedRequests qs) tail.
Proof.
  induction qs as [| q qs IH] in prefix |- *.
  - cbn [protocolFlushes expectedRequests map concat app]. rewrite app_nil_r. reflexivity.
  - cbn [protocolFlushes app].
    replace (expectedResponses (q :: qs ++ rest) F S) with
      (expectedResponses (q :: qs) F S ++ expectedResponses rest F S)
      by (symmetry; exact (responses_app (q :: qs) rest F S)).
    rewrite <- app_assoc, IH. f_equal.
    cbn [expectedRequests map concat]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma protocol_complete qs F S prefix : protocolFlushes qs F S prefix [] = expectedQueryFlushes qs F S prefix.
Proof. induction qs as [| q qs IH] in prefix |- *; cbn [protocolFlushes expectedQueryFlushes]; [reflexivity |].
  rewrite app_nil_r, IH. reflexivity. Qed.
Definition emitted n c i := wireQueries (emit_query n c i).
Definition scoreAt n c F S i := (match c with Finland => extend n F | Sweden => extend n S end) i.
Lemma score_fits value (h : (value <= 1000000001)%nat) : (value < 2^64)%nat.
Proof.
  assert (h16 : (2^16)%nat = 65536%nat) by (vm_compute; reflexivity).
  assert (h32 : (1000000001 < 2^32)%nat).
  { replace 32%nat with (16+16)%nat by reflexivity. rewrite Nat.pow_add_r, h16.
    cbn [Init.Nat.of_num_uint Init.Nat.of_uint Init.Nat.of_uint_acc]. rewrite !Nat.tail_mul_spec. nia. }
  pose proof (Nat.pow_lt_mono_r 2 32 64 ltac:(lia) ltac:(lia)).
  cbn [Init.Nat.of_num_uint Init.Nat.of_uint Init.Nat.of_uint_acc] in *.
  rewrite !Nat.tail_mul_spec in *. lia.
Qed.
Lemma extend_end n F : extend n F (S n) = 0%nat.
Proof.
  unfold extend.
  assert (hz : (S n =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
  assert (he : (S n <=? n)%nat = false) by (apply Nat.leb_gt; lia).
  rewrite hz, he. reflexivity.
Qed.
Ltac numeric_lia :=
  cbn [Init.Nat.of_num_uint Init.Nat.of_uint Init.Nat.of_uint_acc] in *;
  rewrite ?Nat.tail_mul_spec in *; lia.
Lemma ceiling_Z : Z.of_nat ceiling = 1000000001.
Proof.
  unfold ceiling. rewrite Nat2Z.inj_succ.
  cbn [Init.Nat.of_num_uint Init.Nat.of_uint Init.Nat.of_uint_acc].
  rewrite !Nat.tail_mul_spec, !Nat2Z.inj_mul. reflexivity.
Qed.
Lemma char_observed char iv rv buffer input prefix obs :
  execObserved (@outputChar arrayIndex2 (arrayType _ environment2) char)
    (scoreState iv rv buffer input prefix, obs) =
  Some (tt, (scoreState iv rv buffer input (prefix ++ [char]), obs)).
Proof. reflexivity. Qed.
Lemma flush_observed iv rv buffer input prefix obs :
  execObserved flushAction (scoreState iv rv buffer input prefix, obs) =
  Some (tt, (scoreState iv rv buffer input prefix,
    obs ++ [{| flushedOutput := prefix; unreadInput := input |}])).
Proof. reflexivity. Qed.
Lemma index_fits n i (hn : (n <= 100000)%nat) (hi : (i <= Datatypes.S n)%nat) : (i < 2^64)%nat.
Proof. apply score_fits. numeric_lia. Qed.
Lemma billion_Z : Z.of_nat 1000000000%nat = 1000000000.
Proof.
  cbn [Init.Nat.of_num_uint Init.Nat.of_uint Init.Nat.of_uint_acc].
  rewrite !Nat.tail_mul_spec, !Nat2Z.inj_mul. reflexivity.
Qed.
Lemma bounded_fits value (h : (value <= 1000000000)%nat) : (value < 2^64)%nat.
Proof.
  apply Nat2Z.inj_le in h. rewrite billion_Z in h.
  apply Nat2Z.inj_lt. rewrite Nat2Z.inj_pow.
  change (Z.of_nat value < 2^64).
  assert (hp : (1000000000 < 2^64)%Z) by (vm_compute; reflexivity). lia.
Qed.
Lemma coerce_succ n (hn : (n <= 100000)%nat) : coerceInt (Z.of_nat n+1) 64 = Z.of_nat (Datatypes.S n).
Proof. rewrite small_coerce by numeric_lia. lia. Qed.
Lemma query_observed n c i F S iv rv buffer tail prefix obs
  (hn : (n <= 100000)%nat) (hi : (i <= Datatypes.S n)%nat)
  (hF : forall j, (1 <= j <= n)%nat -> (F j <= 1000000000)%nat)
  (hS : forall j, (1 <= j <= n)%nat -> (S j <= 1000000000)%nat)
  (hb : length buffer = 20%nat) :
  exists iv' buffer',
    execObserved (queryCall (countryByte c) (Z.of_nat i) (Z.of_nat n))
      (scoreState iv rv buffer (expectedResponses (emitted n c i) F S ++ tail) prefix, obs) =
    Some (tt, (scoreState iv' (Z.of_nat (scoreAt n c F S i)) buffer' tail
        (prefix ++ expectedRequests (emitted n c i)),
      obs ++ protocolFlushes (emitted n c i) F S prefix tail)) /\ length buffer' = 20%nat.
Proof.
  rewrite queryNormalized.
  destruct (Nat.eq_dec i 0%nat) as [-> | hzero].
  - abstract (
      rewrite bool_decide_true by reflexivity;
      unfold emitted, emit_query, wireQueries;
      cbn [Nat.eqb orb map expectedResponses expectedRequests concat protocolFlushes app];
      rewrite !app_nil_r; exists iv, buffer; split;
      [assert (hz : scoreAt n c F S 0 = ceiling) by (destruct c; reflexivity);
       rewrite hz, ceiling_Z; apply store_reply_observed | exact hb]).
  - rewrite bool_decide_false by lia.
    replace (coerceInt (Z.of_nat n+1) 64) with (Z.of_nat (Datatypes.S n))
      by (symmetry; apply coerce_succ; exact hn).
    destruct (Nat.eq_dec i (Datatypes.S n)) as [-> | hend].
    + rewrite bool_decide_true by reflexivity.
      unfold emitted, emit_query, wireQueries.
      assert (hz : (Datatypes.S n =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
      rewrite hz, Nat.eqb_refl.
      cbn [orb map expectedResponses expectedRequests concat protocolFlushes app].
      rewrite !app_nil_r. exists iv, buffer. split; [| exact hb].
      unfold scoreAt. destruct c; rewrite extend_end; apply store_reply_observed.
    + rewrite bool_decide_false by lia.
      assert (hreal : (1 <= i <= n)%nat) by lia.
      assert (hemit : emitted n c i = [(wireCountry c, i)]).
      { unfold emitted, emit_query, wireQueries.
        assert (hz : (i =? 0)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (he : (i =? Datatypes.S n)%nat = false) by (apply Nat.eqb_neq; lia).
        rewrite hz, he. reflexivity. }
      rewrite hemit. cbn [expectedResponses expectedRequests map concat app].
      unfold expectedResponseLine, expectedQueryLine. cbn [fst snd].
      rewrite !app_nil_r.
      rewrite execObserved_bind, char_observed. cbn [optionBind fst snd].
      rewrite execObserved_bind, char_observed. cbn [optionBind fst snd].
      rewrite execObserved_bind.
      destruct (printer_observed i iv rv buffer
        ((decimalBytes ((match wireCountry c with ProtocolFinland => F | ProtocolSweden => S end) i) ++ [10]) ++ tail)
        ((prefix ++ [countryByte c]) ++ [32]) obs
        (index_fits n i hn hi) hb) as (buffer' & printed & bound).
      rewrite printed. cbn [optionBind fst snd].
      rewrite execObserved_bind, char_observed. cbn [optionBind fst snd].
      rewrite execObserved_bind, flush_observed. cbn [optionBind fst snd].
      rewrite execObserved_bind.
      replace ((decimalBytes ((match wireCountry c with ProtocolFinland => F | ProtocolSweden => S end) i) ++ [10]) ++ tail)
        with (decimalBytes ((match wireCountry c with ProtocolFinland => F | ProtocolSweden => S end) i) ++ 10 :: tail)
        by (rewrite <- app_assoc; reflexivity).
      rewrite reader_observed.
      2: { apply bounded_fits. destruct c; cbn [wireCountry]; [apply hF | apply hS]; exact hreal. }
      cbn [optionBind fst snd]. rewrite execObserved_bind, input_observed.
      cbn [optionBind fst snd]. rewrite store_reply_observed.
      exists (Z.of_nat ((match wireCountry c with ProtocolFinland => F | ProtocolSweden => S end) i)), buffer'.
      split; [| exact bound].
      unfold scoreAt. destruct c; rewrite extend_real by exact hreal;
        cbn [wireCountry countryByte protocolFlushes expectedResponses map concat expectedResponseLine expectedQueryLine fst snd app];
        rewrite <- !app_assoc; cbn [app]; unfold expectedResponseLine; cbn [fst snd]; rewrite <- !app_assoc; reflexivity.
Qed.

Definition Emits {R} (code : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue R)
  qs value F S :=
  forall iv rv buffer tail prefix obs, length buffer = 20%nat ->
  exists iv' rv' buffer',
    execObserved code (scoreState iv rv buffer (expectedResponses qs F S ++ tail) prefix, obs) =
    Some (value, (scoreState iv' rv' buffer' tail (prefix ++ expectedRequests qs),
      obs ++ protocolFlushes qs F S prefix tail)) /\ length buffer' = 20%nat.
Lemma emits_done {R} (value : R) F S : Emits (Done _ _ _ value) [] value F S.
Proof.
  intros iv rv buffer tail prefix obs hb. exists iv, rv, buffer.
  cbn [expectedResponses expectedRequests map concat protocolFlushes app].
  rewrite !app_nil_r. split; [reflexivity | exact hb].
Qed.
Lemma emits_bind {A B} (code : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue A)
  (next : A -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue B)
  qs rest value result F S
  (hc : Emits code qs value F S) (hn : Emits (next value) rest result F S) :
  Emits (code >>= next) (qs ++ rest) result F S.
Proof.
  intros iv rv buffer tail prefix obs hb.
  rewrite execObserved_bind, responses_app, <- app_assoc.
  destruct (hc iv rv buffer (expectedResponses rest F S ++ tail) prefix obs hb)
    as (iv1 & rv1 & buf1 & first & bound1).
  rewrite first. cbn [optionBind fst snd].
  destruct (hn iv1 rv1 buf1 tail (prefix ++ expectedRequests qs)
    (obs ++ protocolFlushes qs F S prefix (expectedResponses rest F S ++ tail)) bound1)
    as (iv2 & rv2 & buf2 & second & bound2).
  rewrite second. exists iv2, rv2, buf2. split; [| exact bound2].
  rewrite requests_app, protocol_app, !app_assoc. reflexivity.
Qed.
Definition queryRead n c i :=
  queryCall (countryByte c) (Z.of_nat i) (Z.of_nat n) >>= fun _ =>
  @readArray arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0.
Lemma queryRead_bind {R} n c i
  (next : Z -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue R) :
  (queryCall (countryByte c) (Z.of_nat i) (Z.of_nat n) >>= fun _ =>
    readArray arraydef_0__reply 0 >>= next) = queryRead n c i >>= next.
Proof. unfold queryRead. apply bindAssoc. Qed.
Lemma queryRead_emits n c i F S
  (hn : (n <= 100000)%nat) (hi : (i <= Datatypes.S n)%nat)
  (hF : forall j, (1 <= j <= n)%nat -> (F j <= 1000000000)%nat)
  (hS : forall j, (1 <= j <= n)%nat -> (S j <= 1000000000)%nat) :
  Emits (queryRead n c i) (emitted n c i) (Z.of_nat (scoreAt n c F S i)) F S.
Proof.
  intros iv rv buffer tail prefix obs hb. unfold queryRead. rewrite execObserved_bind.
  destruct (query_observed n c i F S iv rv buffer tail prefix obs hn hi hF hS hb)
    as (iv' & buffer' & executed & bound).
  rewrite executed. cbn [optionBind fst snd]. rewrite reply_observed.
  exists iv', (Z.of_nat (scoreAt n c F S i)), buffer'. split; [reflexivity | exact bound].
Qed.
Fixpoint searchTrace fuel n k F S lo hi : list ProtocolQuery :=
  match fuel with
  | O => []
  | Datatypes.S fuel =>
    if (lo <? hi)%nat then
      let m := ((lo+hi)/2)%nat in
      emitted n Finland (Datatypes.S m) ++ emitted n Sweden (k-m)%nat ++
      if (F (Datatypes.S m) <? S (k-m))%nat then searchTrace fuel n k F S lo m
      else searchTrace fuel n k F S (Datatypes.S m) hi
    else []
  end.
Lemma midpoint_Z lo hi (hlo : (lo <= hi)%nat) (hhi : (hi <= 100000)%nat) :
  coerceInt (Z.of_nat lo+Z.of_nat hi) 64 / 2 = Z.of_nat ((lo+hi)/2)%nat.
Proof. rewrite small_coerce by numeric_lia. rewrite <- Nat2Z.inj_add, Nat2Z.inj_div. reflexivity. Qed.
Lemma coerce_difference k m (hm : (m <= k)%nat) (hk : (k <= 200000)%nat) :
  coerceInt (Z.of_nat k-Z.of_nat m) 64 = Z.of_nat (k-m)%nat.
Proof. rewrite small_coerce by numeric_lia. rewrite Nat2Z.inj_sub by lia. reflexivity. Qed.
Lemma double_bound n k (hn : (n <= 100000)%nat) (hk : (k <= 2*n)%nat) : (k <= 200000)%nat.
Proof. numeric_lia. Qed.
Lemma search_emits fuel n k lo hi F S
  (hb : (lo <= hi /\ hi <= n /\ hi <= k /\ k-lo <= n /\ n <= 100000 /\ k <= 2*n)%nat)
  (hF : forall j, (1 <= j <= n)%nat -> (F j <= 1000000000)%nat)
  (hS : forall j, (1 <= j <= n)%nat -> (S j <= 1000000000)%nat) :
  Emits (searchAction fuel (Z.of_nat n) (Z.of_nat k) (Z.of_nat lo) (Z.of_nat hi))
    (searchTrace fuel n k (extend n F) (extend n S) lo hi)
    (Z.of_nat (search fuel (crossing k (extend n F) (extend n S)) lo hi)) F S.
Proof.
  induction fuel as [| fuel IH] in lo, hi, hb |- *.
  - cbn [searchAction searchTrace search]. apply emits_done.
  - cbn [searchAction searchTrace search].
    destruct (Nat.eq_dec lo hi) as [-> | hne].
    + rewrite bool_decide_true by reflexivity.
      rewrite Nat.ltb_irrefl. apply emits_done.
    + rewrite bool_decide_false by lia.
      assert (hlt : (lo <? hi)%nat = true) by (apply Nat.ltb_lt; lia).
      rewrite hlt, midpoint_Z by lia.
      pose proof (midpoint_bounds lo hi ltac:(lia)) as hm.
      rewrite coerce_succ by lia. rewrite coerce_difference by (try lia; exact (double_bound n k ltac:(lia) ltac:(lia))).
      rewrite (queryRead_bind n Finland (Datatypes.S ((lo+hi)/2))).
      eapply emits_bind; [apply queryRead_emits; try assumption; lia |].
      rewrite (queryRead_bind n Sweden (k-(lo+hi)/2)%nat).
      eapply emits_bind; [apply queryRead_emits; try assumption; lia |].
      cbn [scoreAt]. rewrite compare_nat. unfold crossing.
      destruct ((extend n F (Datatypes.S ((lo+hi)/2)) <? extend n S (k-(lo+hi)/2))%nat);
        apply IH; lia.
Qed.

Definition selectAction n k lo :=
  queryCall 70 lo n >>= fun _ => readArray arraydef_0__reply 0 >>= fun fv =>
  queryCall 83 (coerceInt (k-lo) 64) n >>= fun _ => readArray arraydef_0__reply 0 >>= fun sv =>
  Done (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue Z
    (if bool_decide (sv < fv) then sv else fv).
Definition answerAction score :=
  outputChar 33 >>= fun _ => outputChar 32 >>= fun _ => mappedPrinter score >>= fun _ =>
  outputChar 10 >>= fun _ => flushAction.
Lemma finalDecomposed n k lo : finalAction n k lo = selectAction n k lo >>= answerAction.
Proof.
  unfold finalAction, selectAction, answerAction. rewrite <- bindAssoc.
  f_equal. apply functional_extensionality. intros []. unfold readArray. cbn [bind].
  f_equal. apply functional_extensionality. intro fv. rewrite <- bindAssoc.
  reflexivity.
Qed.
Definition finishQueries n k i := emitted n Finland i ++ emitted n Sweden (k-i)%nat.
Lemma select_emits n k i F S
  (hb : (i <= n /\ i <= k /\ k-i <= n /\ n <= 100000 /\ k <= 2*n)%nat)
  (hF : forall j, (1 <= j <= n)%nat -> (F j <= 1000000000)%nat)
  (hS : forall j, (1 <= j <= n)%nat -> (S j <= 1000000000)%nat) :
  Emits (selectAction (Z.of_nat n) (Z.of_nat k) (Z.of_nat i)) (finishQueries n k i)
    (Z.of_nat (Nat.min (extend n F i) (extend n S (k-i)%nat))) F S.
Proof.
  unfold selectAction.
  rewrite coerce_difference by (try lia; exact (double_bound n k ltac:(lia) ltac:(lia))).
  replace (finishQueries n k i) with
    (emitted n Finland i ++ (emitted n Sweden (k-i)%nat ++ []))
    by (unfold finishQueries; rewrite app_nil_r; reflexivity).
  rewrite (queryRead_bind n Finland i).
  eapply emits_bind; [apply queryRead_emits; try assumption; lia |].
  rewrite (queryRead_bind n Sweden (k-i)%nat).
  eapply emits_bind; [apply queryRead_emits; try assumption; lia |].
  cbn [scoreAt]. rewrite compare_nat.
  destruct (Nat.ltb_spec0 (extend n S (k-i)%nat) (extend n F i)).
  - rewrite Nat.min_r by lia. apply emits_done.
  - rewrite Nat.min_l by lia. apply emits_done.
Qed.
Lemma answer_observed score iv rv buffer input prefix obs
  (hs : (score < 2^64)%nat) (hb : length buffer = 20%nat) :
  exists buffer', execObserved (answerAction (Z.of_nat score))
    (scoreState iv rv buffer input prefix, obs) =
    Some (tt, (scoreState iv rv buffer' input
      (prefix ++ [33;32] ++ decimalBytes score ++ [10]),
      obs ++ [{| flushedOutput := prefix ++ [33;32] ++ decimalBytes score ++ [10]; unreadInput := input |}])) /\
    length buffer' = 20%nat.
Proof.
  unfold answerAction. rewrite execObserved_bind, char_observed. cbn [optionBind fst snd].
  rewrite execObserved_bind, char_observed. cbn [optionBind fst snd].
  rewrite execObserved_bind.
  destruct (printer_observed score iv rv buffer input ((prefix ++ [33]) ++ [32]) obs hs hb)
    as (buffer' & printed & bound).
  rewrite printed. cbn [optionBind fst snd].
  rewrite execObserved_bind, char_observed. cbn [optionBind fst snd]. rewrite flush_observed.
  exists buffer'. split; [| exact bound]. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma wireQueries_app qs rest : wireQueries (qs ++ rest) = wireQueries qs ++ wireQueries rest.
Proof. apply map_app. Qed.
Lemma searchTrace_flat fuel n k F S lo hi :
  searchTrace fuel n k F S lo hi =
  wireQueries (flat_map (probe_queries n k) (probes fuel (crossing k F S) lo hi)).
Proof.
  induction fuel as [| fuel IH] in lo, hi |- *; [reflexivity |].
  cbn [searchTrace probes]. destruct (lo <? hi)%nat; [| reflexivity].
  cbn [flat_map]. rewrite wireQueries_app. unfold probe_queries. rewrite wireQueries_app.
  unfold crossing. destruct (F (Datatypes.S ((lo+hi)/2)) <? S (k-(lo+hi)/2))%nat;
    rewrite IH; rewrite <- app_assoc; reflexivity.
Qed.
Definition allQueries n k F S :=
  searchTrace 17 n k (extend n F) (extend n S) (low n k) (high n k) ++
  finishQueries n k (Submission.KthHighestScore.partition n k (extend n F) (extend n S)).
Lemma allQueries_trace n k F S : allQueries n k F S =
  wireQueries (query_trace n k (extend n F) (extend n S)).
Proof.
  unfold allQueries, query_trace, finishQueries, Submission.KthHighestScore.partition.
  rewrite !wireQueries_app, searchTrace_flat. reflexivity.
Qed.
Local Opaque search searchTrace searchAction.
Lemma computation_emits n k F S
  (hn : (1 <= n <= 100000)%nat) (hk : (1 <= k <= 2*n)%nat)
  (hF : valid_scores n F) (hS : valid_scores n S) :
  Emits (searchAction 17 (Z.of_nat n) (Z.of_nat k) (Z.of_nat (low n k)) (Z.of_nat (high n k)) >>=
    selectAction (Z.of_nat n) (Z.of_nat k))
    (allQueries n k F S) (Z.of_nat (answer n k (extend n F) (extend n S))) F S.
Proof.
  destruct hF as [hFb hFd], hS as [hSb hSd].
  pose proof (feasible_bounds n k ltac:(lia) hk) as bounds.
  assert (hLow : (k-low n k <= n)%nat) by (unfold low; lia).
  unfold allQueries, answer, Submission.KthHighestScore.partition. eapply emits_bind.
  - apply search_emits; [lia | intros j hj; exact (proj2 (hFb j hj)) | intros j hj; exact (proj2 (hSb j hj))].
  - pose proof (partition_correct n k (extend n F) (extend n S) ltac:(lia) hk
      (extend_valid n F hFb hFd) (extend_valid n S hSb hSd) ltac:(lia)) as [bound _].
    apply select_emits.
    + unfold Submission.KthHighestScore.partition in bound. lia.
    + intros j hj; exact (proj2 (hFb j hj)).
    + intros j hj; exact (proj2 (hSb j hj)).
Qed.

Lemma small_nat_fits value (h : (value <= 200000)%nat) : (value < 2^64)%nat.
Proof. apply score_fits. numeric_lia. Qed.
Lemma initial_low n k (hn : (n <= 100000)%nat) (hk : (k <= 2*n)%nat) :
  (if bool_decide (Z.of_nat n < Z.of_nat k) then coerceInt (Z.of_nat k-Z.of_nat n) 64 else 0) =
  Z.of_nat (low n k).
Proof.
  unfold low. destruct (Nat.lt_ge_cases n k) as [h | h].
  - rewrite bool_decide_true by lia. apply coerce_difference; [lia | exact (double_bound n k hn hk)].
  - rewrite bool_decide_false by lia. replace (k-n)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma initial_high n k :
  (if bool_decide (Z.of_nat n < Z.of_nat k) then Z.of_nat n else Z.of_nat k) = Z.of_nat (high n k).
Proof.
  unfold high. destruct (Nat.lt_ge_cases n k) as [h | h].
  - rewrite bool_decide_true by lia. rewrite Nat.min_r by lia. reflexivity.
  - rewrite bool_decide_false by lia. rewrite Nat.min_l by lia. reflexivity.
Qed.
Theorem generated_end_to_end n k F S
  (hn : (1 <= n <= 100000)%nat) (hk : (1 <= k <= 2*n)%nat)
  (hF : valid_scores n F) (hS : valid_scores n S)
  (hScore : (answer n k (extend n F) (extend n S) < 2^64)%nat) :
  endToEnd Trusted.Spec.program (initial n k (allQueries n k F S) F S)
    (outputBytes (allQueries n k F S) (answer n k (extend n F) (extend n S)))
    (flushes (allQueries n k F S) F S (answer n k (extend n F) (extend n S))).
Proof.
  unfold Trusted.Spec.program. rewrite mainNormalized. unfold mainAction, endToEnd.
  change (exists final,
    execObserved (mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun nv =>
      mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun kv =>
      searchAction 17 nv kv (if bool_decide (nv < kv) then coerceInt (kv-nv) 64 else 0)
        (if bool_decide (nv < kv) then nv else kv) >>= finalAction nv kv)
      (scoreState 0 0 (repeat 0 20)
        (decimalBytes n ++ 32 :: (decimalBytes k ++ 10 :: expectedResponses (allQueries n k F S) F S)) [], []) =
      Some (tt, (final, flushes (allQueries n k F S) F S (answer n k (extend n F) (extend n S)))) /\
    stdout final = outputBytes (allQueries n k F S) (answer n k (extend n F) (extend n S)) /\ stdin final = []).
  rewrite execObserved_bind, header_observed by (apply (index_fits n n); lia).
  cbn [optionBind fst snd]. rewrite execObserved_bind, input_observed. cbn [optionBind fst snd].
  rewrite execObserved_bind, reader_observed by (apply small_nat_fits; exact (double_bound n k ltac:(lia) ltac:(lia))).
  cbn [optionBind fst snd]. rewrite execObserved_bind, input_observed. cbn [optionBind fst snd].
  rewrite initial_low by lia. rewrite initial_high.
  set (qs := allQueries n k F S).
  set (result := answer n k (extend n F) (extend n S)).
  assert (hFinal : finalAction (Z.of_nat n) (Z.of_nat k) =
    fun lo => selectAction (Z.of_nat n) (Z.of_nat k) lo >>= answerAction).
  { apply functional_extensionality. intro lo. apply finalDecomposed. }
  rewrite hFinal, bindAssoc.
  rewrite execObserved_bind.
  pose proof (computation_emits n k F S hn hk hF hS) as hRun.
  specialize (hRun (Z.of_nat k) 0 (repeat 0 20) [] [] [] ltac:(reflexivity)).
  rewrite app_nil_r in hRun. cbn [app] in hRun.
  destruct hRun as (iv & rv & buffer & executed & bound).
  fold qs result in executed.
  rewrite executed. cbn [optionBind fst snd].
  destruct (answer_observed result iv rv buffer [] (expectedRequests qs)
    (protocolFlushes qs F S [] []) hScore bound) as (buffer' & printed & bound').
  rewrite printed.
  exists (scoreState iv rv buffer' [] (outputBytes qs result)).
  split; [| split; reflexivity].
  unfold flushes. rewrite protocol_complete. reflexivity.
Qed.
Print Assumptions generated_end_to_end.
