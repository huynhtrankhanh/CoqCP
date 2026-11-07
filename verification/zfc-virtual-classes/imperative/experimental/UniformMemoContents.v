From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From UniformMemoFixture Require Import UniformMemoProgram EffectFrame.
From stdpp Require Import numbers list.
Module UniformMemoContents.
Import EffectFrame.
Definition protected watched :=
 arraydef_0__meta <> watched /\ arraydef_0__sipState <> watched /\ arraydef_0__uniformMemoState <> watched.
Theorem sipRound_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__sipRound bs ns).
Proof. intros [Hm [Hs Hu]] bs ns. unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__sipWord bs ns).
Proof.
 intros Hprotected bs ns. pose proof (sipRound_ro watched Hprotected) as Hround.
 destruct Hprotected as [Hm [Hs Hu]]. unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__formulaHash bs ns).
Proof.
 intros Hprotected bs ns. pose proof (sipRound_ro watched Hprotected) as Hround. pose proof (sipWord_ro watched Hprotected) as Hword.
 destruct Hprotected as [Hm [Hs Hu]]. unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem uniformMemoGet_ro watched : protected watched -> forall bs ns, array_ro watched (funcdef_0__uniformMemoGet bs ns).
Proof.
 intros Hprotected bs ns. pose proof (formulaHash_ro watched Hprotected) as Hhash.
 destruct Hprotected as [Hm [Hs Hu]]. unfold funcdef_0__uniformMemoGet. apply eliminate_ro. unfold funcdef_0__uniformMemoGet_body. ro.
Qed.
Theorem uniformMemoGet_preserves s bs ns final watched : protected watched ->
 exec (funcdef_0__uniformMemoGet bs ns) s = Some (tt,final) ->
 memory final watched = memory s watched.
Proof. intro Hp. apply exec_preserves. now apply uniformMemoGet_ro. Qed.
Theorem uniformMemoGet_preserves_tables s bs ns final :
 exec (funcdef_0__uniformMemoGet bs ns) s = Some (tt,final) ->
 memory final arraydef_0__uniformMemoEntries = memory s arraydef_0__uniformMemoEntries /\
 memory final arraydef_0__uniformMemoBuckets = memory s arraydef_0__uniformMemoBuckets.
Proof.
 intro Hexec. split; eapply uniformMemoGet_preserves; [repeat split; discriminate|exact Hexec|repeat split; discriminate|exact Hexec].
Qed.
End UniformMemoContents.
