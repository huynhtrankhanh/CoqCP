(* Successful execution of the generated entry point under the complete protocol contract. *)
From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding ArrayExecution DecimalDigits.
From Submission Require Import PermutedBinaryStrings PermutedBinaryStringsCode PermutedBinaryStringsIO PermutedBinaryStringsPrinter PermutedBinaryStringsProgram PermutedBinaryStringsObservations PermutedBinaryStringsProtocol.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Logic.FunctionalExtensionality Sorting.Permutation.
Open Scope Z_scope.

Definition pbsMemory value answer buffer : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__input => [value]
  | arraydef_0__answer => answer
  | arraydef_0__printBuffer => buffer end.
Definition pbsState value answer buffer input output : @Machine arrayIndex2 (arrayType _ environment2) :=
  {| memory := pbsMemory value answer buffer; stdin := input; stdout := output |}.
Lemma modify_input value answer buffer newValue :
  modifyArray (pbsMemory value answer buffer) arraydef_0__input 0 newValue = pbsMemory newValue answer buffer.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma modify_answer value answer buffer index newValue :
  modifyArray (pbsMemory value answer buffer) arraydef_0__answer index newValue = pbsMemory value (<[index := newValue]> answer) buffer.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma buffer_state value answer buffer input output newBuffer :
  setBuffer (pbsState value answer buffer input output) newBuffer = pbsState value answer newBuffer input output.
Proof. reflexivity. Qed.
Definition decoded k a := map (fun x => Z.of_nat (decode k (x-1))) a.
Lemma queryCall_exec k x s : exec (queryCall (Z.of_nat x) (Z.of_nat (2^k)%nat)) s =
  Some (tt, withOutput s (stdout s ++ [48 + Z.of_nat (bit k x)])).
Proof.
  unfold queryCall, funcdef_0__queryBit. rewrite exec_eliminate, generated_query_bit. reflexivity.
Qed.
Lemma recordCall_exec k x index s
  (hk : (k < 10)%nat) (hx : (x < 1000)%nat)
  (hi : (index < length (memory s arraydef_0__answer))%nat)
  (ho : nth index (memory s arraydef_0__answer) 0 = Z.of_nat (decode k x)) :
  exec (recordCall (Z.of_nat index) (Z.of_nat (2^k)%nat) (48+Z.of_nat (bit k x))) s =
  Some (tt, withMemory s (modifyArray (memory s) arraydef_0__answer index (Z.of_nat (decode (S k) x)))).
Proof.
  unfold recordCall, funcdef_0__recordBit. rewrite exec_eliminate, generated_decode_step by assumption. reflexivity.
Qed.
Lemma bitReader_exec digit value answer buffer tail output (hd : digit = 0 \/ digit = 1) :
  exec bitReader (pbsState value answer buffer ((48+digit)::tail) output) =
  Some (tt, pbsState (48+digit) answer buffer tail output).
Proof.
  rewrite bitReaderNormalized, exec_bind.
  cbn [readBinary]. unfold charAction. cbn [bind exec step optionBind fst snd stdin withInput pbsState].
  unfold binaryChar. destruct hd as [-> | ->].
  - rewrite bool_decide_true by lia. cbn [orb exec optionBind fst snd].
    change (exec (writeArray arraydef_0__input (Z.of_nat 0) (48+0))
      (pbsState value answer buffer tail output) = Some (tt, pbsState (48+0) answer buffer tail output)).
    rewrite execWrite by (cbn [memory pbsState pbsMemory length]; lia).
    unfold withMemory. cbn [memory stdin stdout pbsState]. rewrite modify_input. reflexivity.
  - rewrite bool_decide_false by lia. rewrite bool_decide_true by lia.
    cbn [orb exec optionBind fst snd].
    change (exec (writeArray arraydef_0__input (Z.of_nat 0) (48+1))
      (pbsState value answer buffer tail output) = Some (tt, pbsState (48+1) answer buffer tail output)).
    rewrite execWrite by (cbn [memory pbsState pbsMemory length]; lia).
    unfold withMemory. cbn [memory stdin stdout pbsState]. rewrite modify_input. reflexivity.
Qed.

Lemma queryLoop_exec n count k s (h : (count <= n)%nat) :
  exec (queryLoop (Z.of_nat n) count (Z.of_nat (2^k)%nat)) s =
  Some (tt, withOutput s (stdout s ++ map (fun i => 48+Z.of_nat (bit k i)) (seq (n-count) count))).
Proof.
  induction count as [| count IH] in s, h |- *.
  - cbn [queryLoop arrayLoop exec seq map]. rewrite app_nil_r. destruct s; reflexivity.
  - unfold queryLoop at 1. cbn [arrayLoop]. rewrite exec_bind.
    replace (Z.of_nat n-Z.of_nat count-1) with (Z.of_nat (n-S count)) by lia.
    rewrite queryCall_exec. cbn [optionBind fst snd].
    fold (queryLoop (Z.of_nat n) count (Z.of_nat (2^k)%nat)).
    rewrite IH by lia. cbn [withOutput stdout].
    replace (n-count)%nat with (S (n-S count)) by lia.
    cbn [seq map]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma receiveLoop_exec k prefix remaining padding value buffer tail output
  (hk : (k < 10)%nat) (hValues : forall x, In x remaining -> (1 <= x <= 1000)%nat)
  (hSize : (length prefix + length remaining + length padding <= 1000)%nat) :
  exists last, exec (receiveLoop (Z.of_nat (length prefix+length remaining)) (length remaining) (Z.of_nat (2^k)%nat))
    (pbsState value (prefix ++ decoded k remaining ++ padding) buffer (bitBytes k remaining ++ tail) output) =
  Some (tt, pbsState last ((prefix ++ decoded (S k) remaining) ++ padding) buffer tail output).
Proof.
  induction remaining as [| x remaining IH] in prefix, value, hValues, hSize |- *.
  - exists value. cbn [receiveLoop arrayLoop exec decoded bitBytes map app]. rewrite app_nil_r. reflexivity.
  - assert (hx : (1 <= x <= 1000)%nat) by (apply hValues; left; reflexivity).
    cbn [length] in *. unfold receiveLoop at 1. cbn [arrayLoop]. rewrite exec_bind.
    cbn [bitBytes decoded map app].
    rewrite exec_bind.
    rewrite bitReader_exec by (pose proof (bit_binary k (x-1)); lia).
    cbn [optionBind fst snd].
    rewrite (execRead arraydef_0__input 0 0) by (cbn [memory pbsState pbsMemory length]; lia).
    cbn [memory pbsState pbsMemory nth].
    replace (Z.of_nat (length prefix+S (length remaining))-Z.of_nat (length remaining)-1)
      with (Z.of_nat (length prefix)) by lia.
    rewrite recordCall_exec.
    2: { exact hk. }
    2: { lia. }
    2: { cbn [memory pbsState pbsMemory arrayType environment2].
      rewrite length_app. cbn [length]. lia. }
    2: { cbn [memory pbsState pbsMemory arrayType environment2]. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
    cbn [optionBind fst snd]. unfold withMemory. cbn [memory stdin stdout pbsState]. rewrite modify_answer.
    cbn [arrayType environment2].
    fold (decoded k remaining) (decoded (S k) remaining) (bitBytes k remaining).
    rewrite insert_app_r_alt by lia. rewrite Nat.sub_diag. cbn [insert list_insert].
    replace (prefix ++ Z.of_nat (decode (S k) (x-1)) :: decoded k remaining ++ padding)
      with ((prefix ++ [Z.of_nat (decode (S k) (x-1))]) ++ decoded k remaining ++ padding)
      by (rewrite <- app_assoc; reflexivity).
    destruct (IH (prefix ++ [Z.of_nat (decode (S k) (x-1))]) (48+Z.of_nat (bit k (x-1)))
      ltac:(intros y hy; apply hValues; right; exact hy)
      ltac:(rewrite length_app; cbn [length]; lia)) as [last executed].
    exists last. rewrite length_app in executed. cbn [length] in executed.
    replace (length prefix+1+length remaining)%nat with (length prefix+S (length remaining))%nat in executed by lia.
    rewrite <- (app_assoc prefix [Z.of_nat (decode (S k) (x-1))] (decoded (S k) remaining)) in executed.
    cbn [app] in executed. exact executed.
Qed.

Lemma printLoop_exec prefix remaining padding value buffer input output
  (hValues : forall x, In x remaining -> (1 <= x <= 1000)%nat)
  (hSize : (length prefix + length remaining + length padding <= 1000)%nat)
  (hBuffer : length buffer = 20%nat) :
  exists buffer', exec (printLoop (Z.of_nat (length prefix+length remaining)) (length remaining))
    (pbsState value (prefix ++ map (fun x => Z.of_nat (x-1)) remaining ++ padding) buffer input output) =
    Some (tt, pbsState value (prefix ++ map (fun x => Z.of_nat (x-1)) remaining ++ padding) buffer' input
      (output ++ concat (map (fun x => 32 :: decimalBytes x) remaining))) /\ length buffer' = 20%nat.
Proof.
  induction remaining as [| x remaining IH] in prefix, buffer, output, hValues, hSize, hBuffer |- *.
  - exists buffer. cbn [printLoop arrayLoop exec map concat]. rewrite app_nil_r. split; [reflexivity | assumption].
  - assert (hx : (1 <= x <= 1000)%nat) by (apply hValues; left; reflexivity).
    cbn [length] in *. unfold printLoop at 1. cbn [arrayLoop]. rewrite exec_bind.
    cbn [outputChar bind exec step optionBind fst snd].
    replace (Z.of_nat (length prefix+S (length remaining))-Z.of_nat (length remaining)-1)
      with (Z.of_nat (length prefix)) by lia.
    rewrite (execRead arraydef_0__answer (length prefix) 0) by
      (cbn [memory withOutput pbsState pbsMemory arrayType environment2]; rewrite !length_app, !length_map; cbn [length]; lia).
    cbn [memory withOutput pbsState pbsMemory map].
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth app arrayType environment2].
    replace (Z.of_nat (x-1)+1) with (Z.of_nat x) by lia.
    rewrite (small_coerce _ 64) by (try (right; reflexivity); lia).
    destruct (printerExecutionAny x
      (withOutput (pbsState value (prefix ++ Z.of_nat (x-1) :: map (fun y => Z.of_nat (y-1)) remaining ++ padding) buffer input output)
        (output ++ [32])) ltac:(assert (1000 < 2^64)%nat by (apply Nat2Z.inj_lt; rewrite Nat2Z.inj_pow; vm_compute; reflexivity); lia)
      ltac:(exact hBuffer)) as [buffer' [printed hBuffer']].
    match goal with |- context [exec ?code ?state] =>
      assert (printedNative : exec code state = Some (tt,
        pbsState value (prefix ++ Z.of_nat (x-1) :: map (fun y => Z.of_nat (y-1)) remaining ++ padding)
          buffer' input ((output ++ [32]) ++ decimalBytes x))) by exact printed
    end.
    cbn [arrayType environment2] in printedNative |- *.
    rewrite printedNative. cbn [optionBind fst snd].
    replace (prefix ++ Z.of_nat (x-1) :: map (fun y => Z.of_nat (y-1)) remaining ++ padding)
      with ((prefix ++ [Z.of_nat (x-1)]) ++ map (fun y => Z.of_nat (y-1)) remaining ++ padding)
      by (rewrite <- app_assoc; reflexivity).
    destruct (IH (prefix ++ [Z.of_nat (x-1)]) buffer' ((output ++ [32]) ++ decimalBytes x)
      ltac:(intros y hy; apply hValues; right; exact hy)
      ltac:(rewrite length_app; cbn [length]; lia) hBuffer') as [buffer'' [executed hBuffer'']].
    rewrite length_app in executed. cbn [length] in executed.
    replace (length prefix+1+length remaining)%nat with (length prefix+S (length remaining))%nat in executed by lia.
    exists buffer''. split; [| exact hBuffer''].
    rewrite <- !app_assoc in executed. cbn [app] in executed.
    cbn [map concat]. rewrite <- !app_assoc. cbn [app]. exact executed.
Qed.

Lemma observed_output c (s : @Machine arrayIndex2 (arrayType _ environment2)) observations : execObserved (outputChar c) (s, observations) =
  Some (tt, (withOutput s (stdout s ++ [c]), observations)).
Proof. reflexivity. Qed.
Lemma observed_flush (s : @Machine arrayIndex2 (arrayType _ environment2)) observations : execObserved flushAction (s, observations) =
  Some (tt, (s, observations ++ [{| flushedOutput := stdout s; unreadInput := stdin s |}])).
Proof. reflexivity. Qed.
Lemma observed_read (s : @Machine arrayIndex2 (arrayType _ environment2)) c tail observations : execObserved charAction (withInput s (c::tail), observations) =
  Some (c, (withInput s tail, observations)).
Proof. destruct s; reflexivity. Qed.

Lemma observed_read_state value answer buffer c tail output observations :
  execObserved charAction (pbsState value answer buffer (c::tail) output, observations) =
  Some (c, (pbsState value answer buffer tail output, observations)).
Proof. reflexivity. Qed.

Lemma roundObserved k a padding value buffer tail output observations
  (hk : (k < 10)%nat) (hValues : forall x, In x a -> (1 <= x <= 1000)%nat)
  (hSize : (length a + length padding <= 1000)%nat) :
  exists last, execObserved (roundCall (Z.of_nat (length a)) (Z.of_nat (2^k)%nat))
    (pbsState value (decoded k a ++ padding) buffer (replyBytes a k ++ tail) output, observations) =
  Some (tt, (pbsState last (decoded (S k) a ++ padding) buffer tail (output ++ queryBytes (length a) k),
    observations ++ [{| flushedOutput := output ++ queryBytes (length a) k;
                        unreadInput := replyBytes a k ++ tail |}])).
Proof.
  rewrite roundNormalized. unfold roundAction.
  rewrite execObserved_bind, observed_output. cbn [optionBind fst snd].
  rewrite execObserved_bind, observed_output. cbn [optionBind fst snd stdout withOutput].
  rewrite execObserved_bind, execObserved_NoFlush by apply queryLoop_NoFlush.
  rewrite Nat2Z.id, queryLoop_exec by lia. cbn [option_map optionBind fst snd stdout withOutput].
  rewrite Nat.sub_diag.
  rewrite execObserved_bind, observed_output. cbn [optionBind fst snd stdout withOutput].
  rewrite execObserved_bind, observed_flush. cbn [optionBind fst snd stdout stdin withOutput].
  unfold replyBytes. rewrite <- app_assoc. cbn [app].
  destruct (receiveLoop_exec k [] a padding value buffer (10::tail)
    ((((output ++ [63]) ++ [32]) ++ map (fun i => 48+Z.of_nat (bit k i)) (seq 0 (length a))) ++ [10])
    hk hValues ltac:(cbn [length]; exact hSize)) as [last received].
  cbn [length app Nat.add] in received.
  rewrite execObserved_bind, execObserved_NoFlush by apply receiveLoop_NoFlush.
  match goal with |- context [exec ?code ?state] =>
    assert (receivedNative : exec code state = Some (tt, pbsState last (decoded (S k) a ++ padding) buffer (10::tail)
      ((((output ++ [63]) ++ [32]) ++ map (fun i => 48+Z.of_nat (bit k i)) (seq 0 (length a))) ++ [10]))) by exact received
  end. rewrite receivedNative. cbn [option_map optionBind fst snd].
  rewrite execObserved_bind.
  rewrite observed_read_state. cbn [optionBind fst snd execObserved].
  exists last. unfold queryBytes, replyBytes. cbn [app]. rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

Lemma roundsObserved fuel k a padding value buffer tail output observations
  (hk : (k+fuel <= 10)%nat) (hValues : forall x, In x a -> (1 <= x <= 1000)%nat)
  (hSize : (length a + length padding <= 1000)%nat) :
  exists last, execObserved (roundsAction fuel (Z.of_nat (length a)) (Z.of_nat (2^k)%nat))
    (pbsState value (decoded k a ++ padding) buffer (roundInputs a k fuel ++ tail) output, observations) =
  Some (tt, (pbsState last (decoded (k+fuel) a ++ padding) buffer tail
    (output ++ roundOutputs (length a) k fuel), observations ++ roundSnapshots a k fuel output tail)).
Proof.
  induction fuel as [| fuel IH] in k, value, output, observations, hk |- *.
  - exists value. cbn [roundsAction roundInputs roundOutputs roundSnapshots execObserved app].
    rewrite Nat.add_0_r, !app_nil_r. reflexivity.
  - cbn [roundsAction roundInputs]. rewrite <- app_assoc.
    rewrite execObserved_bind.
    destruct (roundObserved k a padding value buffer (roundInputs a (S k) fuel ++ tail) output observations
      ltac:(lia) hValues hSize) as [last stepped].
    rewrite stepped. cbn [optionBind fst snd].
    replace (2*Z.of_nat (2^k)%nat) with (Z.of_nat (2^S k)%nat) by (rewrite Nat.pow_succ_r', Nat2Z.inj_mul; reflexivity).
    rewrite (small_coerce _ 64) by
      (try (right; reflexivity); assert (hp : (2^S k <= 1024)%nat) by
        (replace 1024%nat with (2^10)%nat by reflexivity; apply Nat.pow_le_mono_r; lia); lia).
    destruct (IH (S k) last (output ++ queryBytes (length a) k)
      (observations ++ [{| flushedOutput := output ++ queryBytes (length a) k;
                          unreadInput := replyBytes a k ++ roundInputs a (S k) fuel ++ tail |}]) ltac:(lia))
      as [final executed].
    exists final. cbn [roundOutputs roundSnapshots].
    replace (k+S fuel)%nat with (S k+fuel)%nat by lia.
    repeat rewrite <- app_assoc in executed. repeat rewrite <- app_assoc. cbn [app] in executed |- *. exact executed.
Qed.

Lemma printObserved a padding value buffer input output observations
  (hValues : forall x, In x a -> (1 <= x <= 1000)%nat)
  (hSize : (length a + length padding <= 1000)%nat) (hBuffer : length buffer = 20%nat) :
  exists buffer', execObserved (printCall (Z.of_nat (length a)))
    (pbsState value (map (fun x => Z.of_nat (x-1)) a ++ padding) buffer input output, observations) =
  Some (tt, (pbsState value (map (fun x => Z.of_nat (x-1)) a ++ padding) buffer' input (output ++ answerBytes a),
    observations ++ [{| flushedOutput := output ++ answerBytes a; unreadInput := input |}])).
Proof.
  rewrite printNormalized. unfold printAction.
  rewrite execObserved_bind, observed_output. cbn [optionBind fst snd stdout withOutput].
  rewrite execObserved_bind, execObserved_NoFlush by apply printLoop_NoFlush.
  rewrite Nat2Z.id.
  destruct (printLoop_exec [] a padding value buffer input (output ++ [33]) hValues
    ltac:(cbn [length]; exact hSize) hBuffer) as [buffer' [printed _]].
  cbn [length app Nat.add] in printed.
  match goal with |- context [exec ?code ?state] =>
    assert (printedNative : exec code state = Some (tt,
      pbsState value (map (fun x => Z.of_nat (x-1)) a ++ padding) buffer' input
        ((output ++ [33]) ++ concat (map (fun x => 32::decimalBytes x) a)))) by exact printed
  end. rewrite printedNative. cbn [option_map optionBind fst snd].
  rewrite execObserved_bind, observed_output. cbn [optionBind fst snd].
  rewrite observed_flush. exists buffer'. unfold answerBytes.
  cbn [stdout stdin pbsState withOutput]. rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

Lemma decoded_zero a : decoded 0 a = repeat 0%Z (length a).
Proof. induction a as [| x a IH]; cbn [decoded decode map length repeat]; [reflexivity |]. f_equal. exact IH. Qed.
Lemma decoded_ten a (hValues : forall x, In x a -> (1 <= x <= 1000)%nat) :
  decoded 10 a = map (fun x => Z.of_nat (x-1)) a.
Proof.
  unfold decoded. apply map_ext_in. intros x hx. specialize (hValues x hx).
  rewrite decode_mod. change (Z.of_nat ((x-1) mod 1024)%nat = Z.of_nat (x-1)).
  rewrite Nat.mod_small by lia. reflexivity.
Qed.
Lemma initial_memory a (hSize : (length a <= 1000)%nat) :
  arrays _ environment2 = pbsMemory 0 (decoded 0 a ++ repeat 0 (1000-length a)) (repeat 0 20).
Proof.
  rewrite decoded_zero. apply functional_extensionality_dep. intro name. destruct name; try reflexivity.
  change (repeat 0 1000 = repeat 0 (length a) ++ repeat 0 (1000-length a)).
  rewrite <- repeat_app. replace (length a + (1000-length a))%nat with 1000%nat by lia. reflexivity.
Qed.
Lemma observed_get (name : arrayIndex2) index zero (s : @Machine arrayIndex2 (arrayType _ environment2)) observations
  (h : (index < length (memory s name))%nat) :
  execObserved (readArray name (Z.of_nat index)) (s, observations) =
  Some (nth index (memory s name) zero, (s, observations)).
Proof.
  rewrite execObserved_NoFlush by apply read_NoFlush.
  change (exec (readArray name (Z.of_nat index))) with
    (exec (readArray name (Z.of_nat index) >>= fun x => Done _ _ _ x)).
  rewrite (execRead name index zero) by exact h. reflexivity.
Qed.
Theorem generated_end_to_end n a (h : valid n a) : endToEnd program (initial a) (outputBytes a) (flushes a).
Proof.
  assert (hLen : length a = n) by (pose proof (solve_correct n a h); tauto).
  assert (hSize : (length a <= 1000)%nat) by (destruct h as [hn _]; lia).
  assert (hValues : forall x, In x a -> (1 <= x <= 1000)%nat).
  { intros x hx. destruct h as [hn hp]. assert (hr : (1 <= x < 1+n)%nat).
    { apply in_seq. eapply Permutation_in; [exact hp | exact hx]. } lia. }
  assert (h64 : (length a < 2^64)%nat).
  { assert (1000 < 2^64)%nat by (apply Nat2Z.inj_lt; rewrite Nat2Z.inj_pow; vm_compute; reflexivity). lia. }
  unfold endToEnd, program. rewrite mainNormalized. unfold mainAction.
  unfold initial, inputBytes. rewrite (initial_memory a hSize).
  change (exists final, execObserved
    (mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun count =>
       roundsAction 10 count 1 >>= fun _ => printCall count)
    (pbsState 0 (decoded 0 a ++ repeat 0 (1000-length a)) (repeat 0 20)
      (decimalBytes (length a) ++ 10 :: roundInputs a 0 10) [], []) =
    Some (tt, (final, flushes a)) /\ stdout final = outputBytes a /\ stdin final = []).
  rewrite execObserved_bind, execObserved_NoFlush by apply reader_NoFlush.
  pose proof (decimalReaderExecution (length a) 10 (roundInputs a 0 10)
    (pbsState 0 (decoded 0 a ++ repeat 0 (1000-length a)) (repeat 0 20) [] []) h64
    ltac:(reflexivity) ltac:(cbn [memory pbsState pbsMemory length]; lia)) as readN.
  match goal with |- context [exec ?code ?state] =>
    assert (readNative : exec code state = Some (tt,
      pbsState (Z.of_nat (length a)) (decoded 0 a ++ repeat 0 (1000-length a)) (repeat 0 20)
        (roundInputs a 0 10) []))
  end.
  { unfold withMemory, withInput in readN. cbn [memory stdin stdout pbsState] in readN. rewrite modify_input in readN. exact readN. }
  rewrite readNative. cbn [option_map optionBind fst snd].
  rewrite execObserved_bind.
  replace 0%Z with (Z.of_nat 0) at 1 by reflexivity.
  rewrite (observed_get arraydef_0__input 0 0) by (cbn [memory pbsState pbsMemory length]; lia).
  cbn [memory pbsState pbsMemory nth optionBind fst snd].
  rewrite execObserved_bind.
  pose proof (roundsObserved 10 0 a (repeat 0 (1000-length a)) (Z.of_nat (length a)) (repeat 0 20) [] [] []
    ltac:(lia) hValues ltac:(rewrite repeat_length; lia)) as rounded.
  cbn [Nat.add app] in rounded. rewrite app_nil_r in rounded.
  destruct rounded as [last executed].
  match goal with |- context [execObserved ?code ?state] =>
    assert (roundNative : execObserved code state = Some (tt,
      (pbsState last (decoded 10 a ++ repeat 0 (1000-length a)) (repeat 0 20) [] (roundOutputs (length a) 0 10),
       roundSnapshots a 0 10 [] []))) by exact executed
  end. rewrite roundNative. cbn [optionBind fst snd].
  rewrite decoded_ten by exact hValues.
  destruct (printObserved a (repeat 0 (1000-length a)) last (repeat 0 20) [] (roundOutputs (length a) 0 10)
    (roundSnapshots a 0 10 [] []) hValues ltac:(rewrite repeat_length; lia) ltac:(rewrite repeat_length; reflexivity))
    as [buffer printed].
  rewrite printed. eexists. split; [reflexivity |]. split; reflexivity.
Qed.

(* The observed certificate also proves the existing, unobserved framework
   runtime produces the same complete output and consumes the whole input. *)
Theorem generated_runProgram n a (h : valid n a) :
  exists values, runProgram (arrays _ environment2) program (inputBytes a) =
    Some (values, [], outputBytes a).
Proof.
  destruct (endToEnd_erases program (initial a) (outputBytes a) (flushes a)
    (generated_end_to_end n a h)) as [final [executed [output input]]].
  unfold runProgram. rewrite exec_runProgram.
  change (exec program {| memory := arrays _ environment2; stdin := inputBytes a; stdout := [] |})
    with (exec program (initial a)).
  rewrite executed. cbn [optionBind fst snd]. rewrite output, input. eexists. reflexivity.
Qed.

Lemma roundSnapshots_length a k fuel output tail : length (roundSnapshots a k fuel output tail) = fuel.
Proof. induction fuel as [| fuel IH] in k, output |- *; [reflexivity |]. cbn [roundSnapshots length]. rewrite IH. reflexivity. Qed.
Theorem generated_flush_count a : length (flushes a) = 11%nat.
Proof. unfold flushes. rewrite length_app, roundSnapshots_length. reflexivity. Qed.
Print Assumptions generated_end_to_end.
