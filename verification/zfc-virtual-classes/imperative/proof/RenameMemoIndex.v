From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash IndexFrame RenameMemoHit RenameMemoInvariant.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoIndex.
Import IndexExecution SipHashExecution.
Lemma index_frame s m i depth shift arg :
  RenameMemoHit.storage_frame s (IndexFrame.result_state s m i depth shift arg).
Proof.
  split; [intros name Hname Hsip; now apply IndexFrame.result_other|].
  split; [intros cell H0 H10 H21 H28 H31; now apply IndexFrame.result_meta_other|].
  split; [apply IndexFrame.result_meta_length|].
  unfold IndexFrame.result_state. destruct (bool_decide (i<depth)); split; reflexivity.
Qed.
Theorem index_valid s m i depth shift arg count meaning : RenameMemoInvariant.valid s count meaning ->
  RenameMemoInvariant.valid (IndexFrame.result_state s m i depth shift arg) count meaning.
Proof.
  intro Hvalid. apply RenameMemoInvariant.transport with (s:=s); [exact Hvalid|apply index_frame|].
  now rewrite IndexFrame.result_other by discriminate.
Qed.
Lemma index_storage s m i depth shift arg :
  RenameMemoInvariant.storage_frame s (IndexFrame.result_state s m i depth shift arg).
Proof.
  split; [intros name Hname Hsip Hmemo Hscratch; now apply IndexFrame.result_other|].
  split; [intros; apply IndexFrame.result_meta_other; assumption|].
  split; [apply IndexFrame.result_meta_length|]. split; [now rewrite IndexFrame.result_other by discriminate|].
  unfold IndexFrame.result_state. destruct (bool_decide (i<depth)); split; reflexivity.
Qed.
End RenameMemoIndex.
