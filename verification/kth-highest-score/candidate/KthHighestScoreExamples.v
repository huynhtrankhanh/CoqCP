(* Independently written byte transcripts exercise both final sentinel cases
   and a search with more than one probe. These examples are kernel checked
   with the candidate, rather than delegated to an external test script. *)
From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Generated Require Import KthHighestScore.
Require Trusted.Spec.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Definition observeBytes input :=
  option_map (fun result => let final := fst (snd result) in
    (stdout final, stdin final, snd (snd result)))
    (execObserved Trusted.Spec.program
      ({| memory := arrays _ environment2; stdin := input; stdout := [] |}, [])).
Definition F1 : list Z := [70;32;49;10].
Definition F2 : list Z := [70;32;50;10].
Definition S1 : list Z := [83;32;49;10].
Definition S2 : list Z := [83;32;50;10].
Definition answer4 : list Z := [33;32;52;10].
Definition answer3 : list Z := [33;32;51;10].
Definition snapshot output input := {| flushedOutput := output; unreadInput := input |}.

Example finland_largest :
  observeBytes [49;32;49;10;52;10;51;10;52;10] =
  Some (F1 ++ S1 ++ F1 ++ answer4, [],
    [snapshot F1 [52;10;51;10;52;10];
     snapshot (F1 ++ S1) [51;10;52;10];
     snapshot (F1 ++ S1 ++ F1) [52;10];
     snapshot (F1 ++ S1 ++ F1 ++ answer4) []]).
Proof. vm_compute. reflexivity. Qed.

Example sweden_largest :
  observeBytes [49;32;49;10;51;10;52;10;52;10] =
  Some (F1 ++ S1 ++ S1 ++ answer4, [],
    [snapshot F1 [51;10;52;10;52;10];
     snapshot (F1 ++ S1) [52;10;52;10];
     snapshot (F1 ++ S1 ++ S1) [52;10];
     snapshot (F1 ++ S1 ++ S1 ++ answer4) []]).
Proof. vm_compute. reflexivity. Qed.

Example smallest_rank :
  observeBytes [49;32;50;10;52;10;51;10] =
  Some (F1 ++ S1 ++ answer3, [],
    [snapshot F1 [52;10;51;10]; snapshot (F1 ++ S1) [51;10];
     snapshot (F1 ++ S1 ++ answer3) []]).
Proof. vm_compute. reflexivity. Qed.

Example two_probes :
  observeBytes [50;32;50;10;49;10;52;10;53;10;50;10;53;10;52;10] =
  Some (F2 ++ S1 ++ F1 ++ S2 ++ F1 ++ S1 ++ answer4, [],
    [snapshot F2 [49;10;52;10;53;10;50;10;53;10;52;10];
     snapshot (F2 ++ S1) [52;10;53;10;50;10;53;10;52;10];
     snapshot (F2 ++ S1 ++ F1) [53;10;50;10;53;10;52;10];
     snapshot (F2 ++ S1 ++ F1 ++ S2) [50;10;53;10;52;10];
     snapshot (F2 ++ S1 ++ F1 ++ S2 ++ F1) [53;10;52;10];
     snapshot (F2 ++ S1 ++ F1 ++ S2 ++ F1 ++ S1) [52;10];
     snapshot (F2 ++ S1 ++ F1 ++ S2 ++ F1 ++ S1 ++ answer4) []]).
Proof. vm_compute. reflexivity. Qed.

Example rank_rejects_wrong_answer :
  ~ Trusted.Spec.kth_highest 1 1 (fun _ => 3%nat) (fun _ => 4%nat) 3.
Proof. intros [_ count]. vm_compute in count. discriminate. Qed.
