From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From UniformMemoFixture Require Import UniformMemoProgram ArrayLengthFrame.
From stdpp Require Import numbers list.
Module UniformMemoFrame.
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
Theorem uniformMemoGet_ro watched bs ns : array_ro watched (funcdef_0__uniformMemoGet bs ns).
Proof.
 pose proof (formulaHash_ro watched) as Hhash.
 unfold funcdef_0__uniformMemoGet. apply eliminate_ro. unfold funcdef_0__uniformMemoGet_body. ro.
Qed.
Theorem uniformMemoGet_preserves_length s bs ns final watched :
 exec (funcdef_0__uniformMemoGet bs ns) s = Some (tt,final) ->
 length (memory final watched) = length (memory s watched).
Proof. apply exec_preserves. apply uniformMemoGet_ro. Qed.
End UniformMemoFrame.
