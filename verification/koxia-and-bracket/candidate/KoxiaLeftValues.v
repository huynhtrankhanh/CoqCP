From CoqCP Require Import Options Imperative SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaFrames KoxiaFrameLeft KoxiaArena.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Lemma leftSmall_nat nums len cut : nums vardef_0__solve_length=Z.of_nat len ->
  leftSmall nums (Z.of_nat cut)=Z.of_nat (Nat.min len cut).
Proof.
  intro lenEq. unfold leftSmall. rewrite lenEq. destruct (Nat.lt_ge_cases len cut) as [small|large].
  - rewrite bool_decide_true by lia. rewrite Nat.min_l by lia. reflexivity.
  - rewrite bool_decide_false by lia. rewrite Nat.min_r by lia. reflexivity.
Qed.
Lemma leftHigh_nat nums start span len cut : nums vardef_0__solve_l=Z.of_nat start ->
  nums vardef_0__solve_r=Z.of_nat (start+span) -> nums vardef_0__solve_length=Z.of_nat len ->
  Z.of_nat (len+start+span)<18446744073709551616 ->
  leftHigh nums (Z.of_nat cut)=Z.of_nat (savedLength len cut span).
Proof.
  intros leftEq rightEq lenEq addressFit. unfold leftHigh,savedLength. rewrite leftEq,rightEq,lenEq.
  destruct (Nat.ltb cut len) eqn:present.
  - apply Nat.ltb_lt in present. rewrite bool_decide_true by lia.
    rewrite (coerce64_small (Z.of_nat len-Z.of_nat cut)) by lia.
    rewrite (coerce64_small (Z.of_nat len-Z.of_nat cut+Z.of_nat (start+span))) by lia.
    rewrite coerce64_small by lia. lia.
  - apply Nat.ltb_ge in present. rewrite bool_decide_false by lia. reflexivity.
Qed.
Lemma leftConvolveCall_nat nums start span len cut base :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_top=Z.of_nat base ->
  Z.of_nat span<18446744073709551616 ->
  leftConvolveCall nums (Z.of_nat cut)=
    funcdef_0__convolve (fun _=>false)
      (update (update (update (update (fun _=>0) vardef_0__convolve_skip (Z.of_nat cut))
        vardef_0__convolve_length (Z.of_nat len)) vardef_0__convolve_span (Z.of_nat span))
        vardef_0__convolve_base (Z.of_nat base)).
Proof.
  intros leftEq rightEq lenEq topEq addressFit. unfold leftConvolveCall.
  rewrite leftEq,rightEq,lenEq,topEq. rewrite coerce64_small by lia.
  replace (Z.of_nat (start+span)-Z.of_nat start) with (Z.of_nat span) by lia. reflexivity.
Qed.
Theorem leftFinishedNums_fields nums start span len cut base depth :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_top=Z.of_nat base ->
  nums vardef_0__solve_depth=Z.of_nat depth ->
  Z.of_nat (len+start+span)<18446744073709551616 ->
  Z.of_nat (base+savedLength len cut span)<18446744073709551616 ->
  Z.of_nat (S depth)<18446744073709551616 ->
  leftFinishedNums nums (Z.of_nat cut) vardef_0__solve_length=Z.of_nat (Nat.min len cut) /\
  leftFinishedNums nums (Z.of_nat cut) vardef_0__solve_top=Z.of_nat (base+savedLength len cut span) /\
  leftFinishedNums nums (Z.of_nat cut) vardef_0__solve_depth=Z.of_nat (S depth).
Proof.
  intros leftEq rightEq lenEq topEq depthEq addressFit arenaFit depthFit.
  unfold leftFinishedNums. normalize_frame_updates.
  rewrite leftSmall_nat with (len:=len) by exact lenEq.
  rewrite leftHigh_nat with (start:=start) (span:=span) (len:=len) by assumption.
  rewrite topEq,depthEq. rewrite (coerce64_small (Z.of_nat base+Z.of_nat (savedLength len cut span))) by lia.
  rewrite (coerce64_small (Z.of_nat depth+1)) by lia. repeat split; lia.
Qed.
Lemma leftFinishedNums_other nums cut name : name<>vardef_0__solve_special -> name<>vardef_0__solve_small ->
  name<>vardef_0__solve_hi -> name<>vardef_0__solve_top -> name<>vardef_0__solve_length -> name<>vardef_0__solve_depth ->
  leftFinishedNums nums cut name=nums name.
Proof. intros. unfold leftFinishedNums,leftPreparedNums. normalize_frame_updates. reflexivity. Qed.
