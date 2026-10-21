From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import ArrayLengthFrame.
From stdpp Require Import numbers list.
Module InternLengths.
Import ArrayLengthFrame.
Theorem sipRound_ro watched bs ns : array_ro watched (funcdef_0__sipRound bs ns).
Proof. unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro watched bs ns : array_ro watched (funcdef_0__sipWord bs ns).
Proof.
  pose proof (sipRound_ro watched) as Hround.
  unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro watched bs ns : array_ro watched (funcdef_0__formulaHash bs ns).
Proof.
  pose proof (sipRound_ro watched) as Hround. pose proof (sipWord_ro watched) as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_ro watched : watched<>arraydef_0__formulaBuckets ->
  forall bs ns, array_ro watched (funcdef_0__rehashFormulas bs ns).
Proof.
  intros Hwatched bs ns. pose proof (formulaHash_ro watched) as Hhash.
  unfold funcdef_0__rehashFormulas. apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_ro watched : watched<>arraydef_0__formulaBuckets -> watched<>arraydef_0__formulas -> watched<>arraydef_0__formulaLinks ->
  forall bs ns, array_ro watched (funcdef_0__intern bs ns).
Proof.
  intros Hb Hf Hl bs ns. pose proof (formulaHash_ro watched) as Hhash. pose proof (rehash_ro watched Hb) as Hrehash.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.
Theorem observed_lengths s bs ns observations final after :
  execObserved (funcdef_0__intern bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory final arraydef_0__sipState)=length (memory s arraydef_0__sipState).
Proof.
  intro Hrun. split.
  - exact (observed_preserves arraydef_0__meta (funcdef_0__intern bs ns) s observations tt final after
      (intern_ro arraydef_0__meta ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) bs ns) Hrun).
  - exact (observed_preserves arraydef_0__sipState (funcdef_0__intern bs ns) s observations tt final after
      (intern_ro arraydef_0__sipState ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) bs ns) Hrun).
Qed.
End InternLengths.
