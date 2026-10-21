From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index HashScan.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ScanFrameExecution.
Import IndexExecution HashScanExecution.
Definition preserved (f g : Frame) :=
  length (memory (machine g) arraydef_0__meta) = length (memory (machine f) arraydef_0__meta) /\
  (forall v, v <> vardef_0__intern_current -> v <> vardef_0__intern_found -> nums g v = nums f v) /\
  bools g = bools f.
Lemma preserved_refl f : preserved f f.
Proof. split; [reflexivity|]. split; reflexivity. Qed.
Lemma preserved_trans f g h : preserved f g -> preserved g h -> preserved f h.
Proof.
  intros [Hl [Hn Hb]] [Hl' [Hn' Hb']]. split; [congruence|].
  split; [intros; now rewrite Hn', Hn by assumption|congruence].
Qed.
Lemma found_preserved f i : preserved f (found_frame f i).
Proof.
  split; [apply store_meta_length|]. split; [|reflexivity].
  intros v Hcurrent Hfound. unfold found_frame, advance.
  cbn [nums setNum setMachine]. unfold Imperative.update.
  repeat case_decide; congruence.
Qed.
Lemma next_preserved f i link : preserved f (next_frame f i link).
Proof.
  split; [reflexivity|]. split; [|reflexivity].
  intros v Hcurrent Hfound. unfold next_frame, advance.
  cbn [nums setNum]. unfold Imperative.update.
  repeat case_decide; congruence.
Qed.
Theorem generated_scan_frame fuel (f : Frame) n pointer final :
  table_valid (machine f) n -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat pointer -> (pointer <= n)%nat ->
  execLocal (loop fuel scan_body) f = Some (tt,final) -> preserved f final.
Proof.
  induction fuel as [|fuel IH] in f, pointer |- *.
  - intros Hvalid Hlimit Hmeta Hpointer Hbound Hrun.
    cbn [loop execLocal] in Hrun. injection Hrun as <-. apply preserved_refl.
  - intros [Hformulas [Hlinks Hdescending]] Hlimit Hmeta Hpointer Hbound Hrun.
    rewrite loop_S, execLocal_bind in Hrun.
    destruct pointer as [|i].
    + rewrite scan_empty in Hrun by exact Hpointer. cbn [optionBind fst snd] in Hrun.
      injection Hrun as <-. apply preserved_refl.
    + destruct (List.nth i (memory (machine f) arraydef_0__formulas) (0,0,0)) as [[x y] z] eqn:Hentry.
      set (link := List.nth i (memory (machine f) arraydef_0__formulaLinks) 0).
      rewrite (scan_step f fuel i x y z link Hpointer) in Hrun by (try assumption; try reflexivity; lia).
      destruct (bool_decide ((x,y,z) = sought f)) eqn:Hmatch; cbn [optionBind fst snd] in Hrun.
      * injection Hrun as <-. apply found_preserved.
      * apply (preserved_trans _ (next_frame f i link)); [apply next_preserved|].
        apply (IH (next_frame f i link) (Z.to_nat link)); try assumption.
        -- split; [exact Hformulas|]. split; assumption.
        -- change (link = Z.of_nat (Z.to_nat link)). rewrite Z2Nat.id; [reflexivity|]. apply Hdescending; lia.
        -- pose proof (Hdescending i ltac:(lia)) as Hlink. fold link in Hlink.
           pose proof (Z2Nat.id link ltac:(lia)). lia.
Qed.
End ScanFrameExecution.
