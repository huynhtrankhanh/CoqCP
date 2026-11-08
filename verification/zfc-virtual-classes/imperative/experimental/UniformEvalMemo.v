From CoqCP Require Import Options Imperative Execution.
From UniformEvalFull Require Import EvalProgram UniformEvalLoop UniformMemoLoop UniformMemoStorage.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

(* Relate the evaluator's actual nested call to the memo procedure's local
   frame. The memo proof and the caller use the same generated environment. *)
Module UniformEvalMemo.
Definition caller_frame := UniformEvalLoop.Frame.
Definition memo_frame (f : caller_frame) : UniformMemoLoop.Frame :=
  {| machine := machine f;
     bools := fun _ => false;
     nums := update (update (fun _ => 0) vardef_0__uniformMemoGet_node
       (nums f vardef_0__uniformEvaluate_node)) vardef_0__uniformMemoGet_depth
       (nums f vardef_0__uniformEvaluate_depth) |}.

Lemma actual_memo_call (f : caller_frame) :
  execLocal UniformEvalLoop.memo_get_call f =
  optionBind (execLocal funcdef_0__uniformMemoGet_body (memo_frame f))
    (fun r => Some (fst r, setMachine f (machine (snd r)))).
Proof.
  destruct f as [s bs ns].
  unfold UniformEvalLoop.memo_get_call, memo_frame. cbn zeta.
  cbv beta iota zeta delta [numberLocalGet bind execLocal localStep optionBind
                            fst snd nums bools machine].
  change (execLocal (liftToWithLocalVariables (funcdef_0__uniformMemoGet
    (fun _ => false)
    (update (update (fun _ => 0) vardef_0__uniformMemoGet_node
      (ns vardef_0__uniformEvaluate_node)) vardef_0__uniformMemoGet_depth
      (ns vardef_0__uniformEvaluate_depth)))) {| machine := s; bools := bs; nums := ns |} = _).
  rewrite execLocal_lift. unfold funcdef_0__uniformMemoGet.
  rewrite exec_eliminate. destruct (execLocal _ _) as [[[] after]|]; reflexivity.
Qed.
End UniformEvalMemo.
