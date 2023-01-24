From stdpp Require Import numbers list.
From CoqCP Require Import PropertyPreservedAfterSorting.

Lemma bubbleSortTestTheorem0 : bubbleSortDemo [0; 1; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem1 : bubbleSortDemo [0; 2; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem2 : bubbleSortDemo [1; 0; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem3 : bubbleSortDemo [1; 2; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem4 : bubbleSortDemo [2; 0; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem5 : bubbleSortDemo [2; 1; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem6 : bubbleSortDemo [0; 1; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem7 : bubbleSortDemo [0; 1; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem8 : bubbleSortDemo [0; 2; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem9 : bubbleSortDemo [0; 2; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem10 : bubbleSortDemo [0; 3; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem11 : bubbleSortDemo [0; 3; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem12 : bubbleSortDemo [1; 0; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem13 : bubbleSortDemo [1; 0; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem14 : bubbleSortDemo [1; 2; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem15 : bubbleSortDemo [1; 2; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem16 : bubbleSortDemo [1; 3; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem17 : bubbleSortDemo [1; 3; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem18 : bubbleSortDemo [2; 0; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem19 : bubbleSortDemo [2; 0; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem20 : bubbleSortDemo [2; 1; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem21 : bubbleSortDemo [2; 1; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem22 : bubbleSortDemo [2; 3; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem23 : bubbleSortDemo [2; 3; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem24 : bubbleSortDemo [3; 0; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem25 : bubbleSortDemo [3; 0; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem26 : bubbleSortDemo [3; 1; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem27 : bubbleSortDemo [3; 1; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem28 : bubbleSortDemo [3; 2; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem29 : bubbleSortDemo [3; 2; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem30 : bubbleSortDemo [0; 1; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem31 : bubbleSortDemo [0; 1; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem32 : bubbleSortDemo [0; 1; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem33 : bubbleSortDemo [0; 1; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem34 : bubbleSortDemo [0; 1; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem35 : bubbleSortDemo [0; 1; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem36 : bubbleSortDemo [0; 2; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem37 : bubbleSortDemo [0; 2; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem38 : bubbleSortDemo [0; 2; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem39 : bubbleSortDemo [0; 2; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem40 : bubbleSortDemo [0; 2; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem41 : bubbleSortDemo [0; 2; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem42 : bubbleSortDemo [0; 3; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem43 : bubbleSortDemo [0; 3; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem44 : bubbleSortDemo [0; 3; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem45 : bubbleSortDemo [0; 3; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem46 : bubbleSortDemo [0; 3; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem47 : bubbleSortDemo [0; 3; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem48 : bubbleSortDemo [0; 4; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem49 : bubbleSortDemo [0; 4; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem50 : bubbleSortDemo [0; 4; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem51 : bubbleSortDemo [0; 4; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem52 : bubbleSortDemo [0; 4; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem53 : bubbleSortDemo [0; 4; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem54 : bubbleSortDemo [1; 0; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem55 : bubbleSortDemo [1; 0; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem56 : bubbleSortDemo [1; 0; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem57 : bubbleSortDemo [1; 0; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem58 : bubbleSortDemo [1; 0; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem59 : bubbleSortDemo [1; 0; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem60 : bubbleSortDemo [1; 2; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem61 : bubbleSortDemo [1; 2; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem62 : bubbleSortDemo [1; 2; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem63 : bubbleSortDemo [1; 2; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem64 : bubbleSortDemo [1; 2; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem65 : bubbleSortDemo [1; 2; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem66 : bubbleSortDemo [1; 3; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem67 : bubbleSortDemo [1; 3; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem68 : bubbleSortDemo [1; 3; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem69 : bubbleSortDemo [1; 3; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem70 : bubbleSortDemo [1; 3; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem71 : bubbleSortDemo [1; 3; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem72 : bubbleSortDemo [1; 4; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem73 : bubbleSortDemo [1; 4; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem74 : bubbleSortDemo [1; 4; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem75 : bubbleSortDemo [1; 4; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem76 : bubbleSortDemo [1; 4; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem77 : bubbleSortDemo [1; 4; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem78 : bubbleSortDemo [2; 0; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem79 : bubbleSortDemo [2; 0; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem80 : bubbleSortDemo [2; 0; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem81 : bubbleSortDemo [2; 0; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem82 : bubbleSortDemo [2; 0; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem83 : bubbleSortDemo [2; 0; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem84 : bubbleSortDemo [2; 1; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem85 : bubbleSortDemo [2; 1; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem86 : bubbleSortDemo [2; 1; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem87 : bubbleSortDemo [2; 1; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem88 : bubbleSortDemo [2; 1; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem89 : bubbleSortDemo [2; 1; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem90 : bubbleSortDemo [2; 3; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem91 : bubbleSortDemo [2; 3; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem92 : bubbleSortDemo [2; 3; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem93 : bubbleSortDemo [2; 3; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem94 : bubbleSortDemo [2; 3; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem95 : bubbleSortDemo [2; 3; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem96 : bubbleSortDemo [2; 4; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem97 : bubbleSortDemo [2; 4; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem98 : bubbleSortDemo [2; 4; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem99 : bubbleSortDemo [2; 4; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem100 : bubbleSortDemo [2; 4; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem101 : bubbleSortDemo [2; 4; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem102 : bubbleSortDemo [3; 0; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem103 : bubbleSortDemo [3; 0; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem104 : bubbleSortDemo [3; 0; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem105 : bubbleSortDemo [3; 0; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem106 : bubbleSortDemo [3; 0; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem107 : bubbleSortDemo [3; 0; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem108 : bubbleSortDemo [3; 1; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem109 : bubbleSortDemo [3; 1; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem110 : bubbleSortDemo [3; 1; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem111 : bubbleSortDemo [3; 1; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem112 : bubbleSortDemo [3; 1; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem113 : bubbleSortDemo [3; 1; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem114 : bubbleSortDemo [3; 2; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem115 : bubbleSortDemo [3; 2; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem116 : bubbleSortDemo [3; 2; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem117 : bubbleSortDemo [3; 2; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem118 : bubbleSortDemo [3; 2; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem119 : bubbleSortDemo [3; 2; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem120 : bubbleSortDemo [3; 4; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem121 : bubbleSortDemo [3; 4; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem122 : bubbleSortDemo [3; 4; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem123 : bubbleSortDemo [3; 4; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem124 : bubbleSortDemo [3; 4; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem125 : bubbleSortDemo [3; 4; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem126 : bubbleSortDemo [4; 0; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem127 : bubbleSortDemo [4; 0; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem128 : bubbleSortDemo [4; 0; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem129 : bubbleSortDemo [4; 0; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem130 : bubbleSortDemo [4; 0; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem131 : bubbleSortDemo [4; 0; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem132 : bubbleSortDemo [4; 1; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem133 : bubbleSortDemo [4; 1; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem134 : bubbleSortDemo [4; 1; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem135 : bubbleSortDemo [4; 1; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem136 : bubbleSortDemo [4; 1; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem137 : bubbleSortDemo [4; 1; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem138 : bubbleSortDemo [4; 2; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem139 : bubbleSortDemo [4; 2; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem140 : bubbleSortDemo [4; 2; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem141 : bubbleSortDemo [4; 2; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem142 : bubbleSortDemo [4; 2; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem143 : bubbleSortDemo [4; 2; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem144 : bubbleSortDemo [4; 3; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem145 : bubbleSortDemo [4; 3; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem146 : bubbleSortDemo [4; 3; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem147 : bubbleSortDemo [4; 3; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem148 : bubbleSortDemo [4; 3; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem149 : bubbleSortDemo [4; 3; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem150 : bubbleSortDemo [0; 1; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem151 : bubbleSortDemo [0; 1; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem152 : bubbleSortDemo [0; 1; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem153 : bubbleSortDemo [0; 1; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem154 : bubbleSortDemo [0; 1; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem155 : bubbleSortDemo [0; 1; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem156 : bubbleSortDemo [0; 1; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem157 : bubbleSortDemo [0; 1; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem158 : bubbleSortDemo [0; 1; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem159 : bubbleSortDemo [0; 1; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem160 : bubbleSortDemo [0; 1; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem161 : bubbleSortDemo [0; 1; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem162 : bubbleSortDemo [0; 1; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem163 : bubbleSortDemo [0; 1; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem164 : bubbleSortDemo [0; 1; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem165 : bubbleSortDemo [0; 1; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem166 : bubbleSortDemo [0; 1; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem167 : bubbleSortDemo [0; 1; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem168 : bubbleSortDemo [0; 1; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem169 : bubbleSortDemo [0; 1; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem170 : bubbleSortDemo [0; 1; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem171 : bubbleSortDemo [0; 1; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem172 : bubbleSortDemo [0; 1; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem173 : bubbleSortDemo [0; 1; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem174 : bubbleSortDemo [0; 2; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem175 : bubbleSortDemo [0; 2; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem176 : bubbleSortDemo [0; 2; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem177 : bubbleSortDemo [0; 2; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem178 : bubbleSortDemo [0; 2; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem179 : bubbleSortDemo [0; 2; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem180 : bubbleSortDemo [0; 2; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem181 : bubbleSortDemo [0; 2; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem182 : bubbleSortDemo [0; 2; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem183 : bubbleSortDemo [0; 2; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem184 : bubbleSortDemo [0; 2; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem185 : bubbleSortDemo [0; 2; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem186 : bubbleSortDemo [0; 2; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem187 : bubbleSortDemo [0; 2; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem188 : bubbleSortDemo [0; 2; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem189 : bubbleSortDemo [0; 2; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem190 : bubbleSortDemo [0; 2; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem191 : bubbleSortDemo [0; 2; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem192 : bubbleSortDemo [0; 2; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem193 : bubbleSortDemo [0; 2; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem194 : bubbleSortDemo [0; 2; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem195 : bubbleSortDemo [0; 2; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem196 : bubbleSortDemo [0; 2; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem197 : bubbleSortDemo [0; 2; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem198 : bubbleSortDemo [0; 3; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem199 : bubbleSortDemo [0; 3; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem200 : bubbleSortDemo [0; 3; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem201 : bubbleSortDemo [0; 3; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem202 : bubbleSortDemo [0; 3; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem203 : bubbleSortDemo [0; 3; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem204 : bubbleSortDemo [0; 3; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem205 : bubbleSortDemo [0; 3; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem206 : bubbleSortDemo [0; 3; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem207 : bubbleSortDemo [0; 3; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem208 : bubbleSortDemo [0; 3; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem209 : bubbleSortDemo [0; 3; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem210 : bubbleSortDemo [0; 3; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem211 : bubbleSortDemo [0; 3; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem212 : bubbleSortDemo [0; 3; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem213 : bubbleSortDemo [0; 3; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem214 : bubbleSortDemo [0; 3; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem215 : bubbleSortDemo [0; 3; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem216 : bubbleSortDemo [0; 3; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem217 : bubbleSortDemo [0; 3; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem218 : bubbleSortDemo [0; 3; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem219 : bubbleSortDemo [0; 3; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem220 : bubbleSortDemo [0; 3; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem221 : bubbleSortDemo [0; 3; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem222 : bubbleSortDemo [0; 4; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem223 : bubbleSortDemo [0; 4; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem224 : bubbleSortDemo [0; 4; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem225 : bubbleSortDemo [0; 4; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem226 : bubbleSortDemo [0; 4; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem227 : bubbleSortDemo [0; 4; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem228 : bubbleSortDemo [0; 4; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem229 : bubbleSortDemo [0; 4; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem230 : bubbleSortDemo [0; 4; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem231 : bubbleSortDemo [0; 4; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem232 : bubbleSortDemo [0; 4; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem233 : bubbleSortDemo [0; 4; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem234 : bubbleSortDemo [0; 4; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem235 : bubbleSortDemo [0; 4; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem236 : bubbleSortDemo [0; 4; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem237 : bubbleSortDemo [0; 4; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem238 : bubbleSortDemo [0; 4; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem239 : bubbleSortDemo [0; 4; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem240 : bubbleSortDemo [0; 4; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem241 : bubbleSortDemo [0; 4; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem242 : bubbleSortDemo [0; 4; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem243 : bubbleSortDemo [0; 4; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem244 : bubbleSortDemo [0; 4; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem245 : bubbleSortDemo [0; 4; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem246 : bubbleSortDemo [0; 5; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem247 : bubbleSortDemo [0; 5; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem248 : bubbleSortDemo [0; 5; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem249 : bubbleSortDemo [0; 5; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem250 : bubbleSortDemo [0; 5; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem251 : bubbleSortDemo [0; 5; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem252 : bubbleSortDemo [0; 5; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem253 : bubbleSortDemo [0; 5; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem254 : bubbleSortDemo [0; 5; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem255 : bubbleSortDemo [0; 5; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem256 : bubbleSortDemo [0; 5; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem257 : bubbleSortDemo [0; 5; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem258 : bubbleSortDemo [0; 5; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem259 : bubbleSortDemo [0; 5; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem260 : bubbleSortDemo [0; 5; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem261 : bubbleSortDemo [0; 5; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem262 : bubbleSortDemo [0; 5; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem263 : bubbleSortDemo [0; 5; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem264 : bubbleSortDemo [0; 5; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem265 : bubbleSortDemo [0; 5; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem266 : bubbleSortDemo [0; 5; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem267 : bubbleSortDemo [0; 5; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem268 : bubbleSortDemo [0; 5; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem269 : bubbleSortDemo [0; 5; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem270 : bubbleSortDemo [1; 0; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem271 : bubbleSortDemo [1; 0; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem272 : bubbleSortDemo [1; 0; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem273 : bubbleSortDemo [1; 0; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem274 : bubbleSortDemo [1; 0; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem275 : bubbleSortDemo [1; 0; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem276 : bubbleSortDemo [1; 0; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem277 : bubbleSortDemo [1; 0; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem278 : bubbleSortDemo [1; 0; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem279 : bubbleSortDemo [1; 0; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem280 : bubbleSortDemo [1; 0; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem281 : bubbleSortDemo [1; 0; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem282 : bubbleSortDemo [1; 0; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem283 : bubbleSortDemo [1; 0; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem284 : bubbleSortDemo [1; 0; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem285 : bubbleSortDemo [1; 0; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem286 : bubbleSortDemo [1; 0; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem287 : bubbleSortDemo [1; 0; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem288 : bubbleSortDemo [1; 0; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem289 : bubbleSortDemo [1; 0; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem290 : bubbleSortDemo [1; 0; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem291 : bubbleSortDemo [1; 0; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem292 : bubbleSortDemo [1; 0; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem293 : bubbleSortDemo [1; 0; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem294 : bubbleSortDemo [1; 2; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem295 : bubbleSortDemo [1; 2; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem296 : bubbleSortDemo [1; 2; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem297 : bubbleSortDemo [1; 2; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem298 : bubbleSortDemo [1; 2; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem299 : bubbleSortDemo [1; 2; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem300 : bubbleSortDemo [1; 2; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem301 : bubbleSortDemo [1; 2; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem302 : bubbleSortDemo [1; 2; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem303 : bubbleSortDemo [1; 2; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem304 : bubbleSortDemo [1; 2; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem305 : bubbleSortDemo [1; 2; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem306 : bubbleSortDemo [1; 2; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem307 : bubbleSortDemo [1; 2; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem308 : bubbleSortDemo [1; 2; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem309 : bubbleSortDemo [1; 2; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem310 : bubbleSortDemo [1; 2; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem311 : bubbleSortDemo [1; 2; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem312 : bubbleSortDemo [1; 2; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem313 : bubbleSortDemo [1; 2; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem314 : bubbleSortDemo [1; 2; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem315 : bubbleSortDemo [1; 2; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem316 : bubbleSortDemo [1; 2; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem317 : bubbleSortDemo [1; 2; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem318 : bubbleSortDemo [1; 3; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem319 : bubbleSortDemo [1; 3; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem320 : bubbleSortDemo [1; 3; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem321 : bubbleSortDemo [1; 3; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem322 : bubbleSortDemo [1; 3; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem323 : bubbleSortDemo [1; 3; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem324 : bubbleSortDemo [1; 3; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem325 : bubbleSortDemo [1; 3; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem326 : bubbleSortDemo [1; 3; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem327 : bubbleSortDemo [1; 3; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem328 : bubbleSortDemo [1; 3; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem329 : bubbleSortDemo [1; 3; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem330 : bubbleSortDemo [1; 3; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem331 : bubbleSortDemo [1; 3; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem332 : bubbleSortDemo [1; 3; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem333 : bubbleSortDemo [1; 3; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem334 : bubbleSortDemo [1; 3; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem335 : bubbleSortDemo [1; 3; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem336 : bubbleSortDemo [1; 3; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem337 : bubbleSortDemo [1; 3; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem338 : bubbleSortDemo [1; 3; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem339 : bubbleSortDemo [1; 3; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem340 : bubbleSortDemo [1; 3; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem341 : bubbleSortDemo [1; 3; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem342 : bubbleSortDemo [1; 4; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem343 : bubbleSortDemo [1; 4; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem344 : bubbleSortDemo [1; 4; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem345 : bubbleSortDemo [1; 4; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem346 : bubbleSortDemo [1; 4; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem347 : bubbleSortDemo [1; 4; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem348 : bubbleSortDemo [1; 4; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem349 : bubbleSortDemo [1; 4; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem350 : bubbleSortDemo [1; 4; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem351 : bubbleSortDemo [1; 4; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem352 : bubbleSortDemo [1; 4; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem353 : bubbleSortDemo [1; 4; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem354 : bubbleSortDemo [1; 4; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem355 : bubbleSortDemo [1; 4; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem356 : bubbleSortDemo [1; 4; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem357 : bubbleSortDemo [1; 4; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem358 : bubbleSortDemo [1; 4; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem359 : bubbleSortDemo [1; 4; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem360 : bubbleSortDemo [1; 4; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem361 : bubbleSortDemo [1; 4; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem362 : bubbleSortDemo [1; 4; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem363 : bubbleSortDemo [1; 4; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem364 : bubbleSortDemo [1; 4; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem365 : bubbleSortDemo [1; 4; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem366 : bubbleSortDemo [1; 5; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem367 : bubbleSortDemo [1; 5; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem368 : bubbleSortDemo [1; 5; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem369 : bubbleSortDemo [1; 5; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem370 : bubbleSortDemo [1; 5; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem371 : bubbleSortDemo [1; 5; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem372 : bubbleSortDemo [1; 5; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem373 : bubbleSortDemo [1; 5; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem374 : bubbleSortDemo [1; 5; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem375 : bubbleSortDemo [1; 5; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem376 : bubbleSortDemo [1; 5; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem377 : bubbleSortDemo [1; 5; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem378 : bubbleSortDemo [1; 5; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem379 : bubbleSortDemo [1; 5; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem380 : bubbleSortDemo [1; 5; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem381 : bubbleSortDemo [1; 5; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem382 : bubbleSortDemo [1; 5; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem383 : bubbleSortDemo [1; 5; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem384 : bubbleSortDemo [1; 5; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem385 : bubbleSortDemo [1; 5; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem386 : bubbleSortDemo [1; 5; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem387 : bubbleSortDemo [1; 5; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem388 : bubbleSortDemo [1; 5; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem389 : bubbleSortDemo [1; 5; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem390 : bubbleSortDemo [2; 0; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem391 : bubbleSortDemo [2; 0; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem392 : bubbleSortDemo [2; 0; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem393 : bubbleSortDemo [2; 0; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem394 : bubbleSortDemo [2; 0; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem395 : bubbleSortDemo [2; 0; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem396 : bubbleSortDemo [2; 0; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem397 : bubbleSortDemo [2; 0; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem398 : bubbleSortDemo [2; 0; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem399 : bubbleSortDemo [2; 0; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem400 : bubbleSortDemo [2; 0; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem401 : bubbleSortDemo [2; 0; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem402 : bubbleSortDemo [2; 0; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem403 : bubbleSortDemo [2; 0; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem404 : bubbleSortDemo [2; 0; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem405 : bubbleSortDemo [2; 0; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem406 : bubbleSortDemo [2; 0; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem407 : bubbleSortDemo [2; 0; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem408 : bubbleSortDemo [2; 0; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem409 : bubbleSortDemo [2; 0; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem410 : bubbleSortDemo [2; 0; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem411 : bubbleSortDemo [2; 0; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem412 : bubbleSortDemo [2; 0; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem413 : bubbleSortDemo [2; 0; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem414 : bubbleSortDemo [2; 1; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem415 : bubbleSortDemo [2; 1; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem416 : bubbleSortDemo [2; 1; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem417 : bubbleSortDemo [2; 1; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem418 : bubbleSortDemo [2; 1; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem419 : bubbleSortDemo [2; 1; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem420 : bubbleSortDemo [2; 1; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem421 : bubbleSortDemo [2; 1; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem422 : bubbleSortDemo [2; 1; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem423 : bubbleSortDemo [2; 1; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem424 : bubbleSortDemo [2; 1; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem425 : bubbleSortDemo [2; 1; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem426 : bubbleSortDemo [2; 1; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem427 : bubbleSortDemo [2; 1; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem428 : bubbleSortDemo [2; 1; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem429 : bubbleSortDemo [2; 1; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem430 : bubbleSortDemo [2; 1; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem431 : bubbleSortDemo [2; 1; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem432 : bubbleSortDemo [2; 1; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem433 : bubbleSortDemo [2; 1; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem434 : bubbleSortDemo [2; 1; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem435 : bubbleSortDemo [2; 1; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem436 : bubbleSortDemo [2; 1; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem437 : bubbleSortDemo [2; 1; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem438 : bubbleSortDemo [2; 3; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem439 : bubbleSortDemo [2; 3; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem440 : bubbleSortDemo [2; 3; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem441 : bubbleSortDemo [2; 3; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem442 : bubbleSortDemo [2; 3; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem443 : bubbleSortDemo [2; 3; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem444 : bubbleSortDemo [2; 3; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem445 : bubbleSortDemo [2; 3; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem446 : bubbleSortDemo [2; 3; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem447 : bubbleSortDemo [2; 3; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem448 : bubbleSortDemo [2; 3; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem449 : bubbleSortDemo [2; 3; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem450 : bubbleSortDemo [2; 3; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem451 : bubbleSortDemo [2; 3; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem452 : bubbleSortDemo [2; 3; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem453 : bubbleSortDemo [2; 3; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem454 : bubbleSortDemo [2; 3; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem455 : bubbleSortDemo [2; 3; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem456 : bubbleSortDemo [2; 3; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem457 : bubbleSortDemo [2; 3; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem458 : bubbleSortDemo [2; 3; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem459 : bubbleSortDemo [2; 3; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem460 : bubbleSortDemo [2; 3; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem461 : bubbleSortDemo [2; 3; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem462 : bubbleSortDemo [2; 4; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem463 : bubbleSortDemo [2; 4; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem464 : bubbleSortDemo [2; 4; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem465 : bubbleSortDemo [2; 4; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem466 : bubbleSortDemo [2; 4; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem467 : bubbleSortDemo [2; 4; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem468 : bubbleSortDemo [2; 4; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem469 : bubbleSortDemo [2; 4; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem470 : bubbleSortDemo [2; 4; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem471 : bubbleSortDemo [2; 4; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem472 : bubbleSortDemo [2; 4; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem473 : bubbleSortDemo [2; 4; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem474 : bubbleSortDemo [2; 4; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem475 : bubbleSortDemo [2; 4; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem476 : bubbleSortDemo [2; 4; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem477 : bubbleSortDemo [2; 4; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem478 : bubbleSortDemo [2; 4; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem479 : bubbleSortDemo [2; 4; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem480 : bubbleSortDemo [2; 4; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem481 : bubbleSortDemo [2; 4; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem482 : bubbleSortDemo [2; 4; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem483 : bubbleSortDemo [2; 4; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem484 : bubbleSortDemo [2; 4; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem485 : bubbleSortDemo [2; 4; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem486 : bubbleSortDemo [2; 5; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem487 : bubbleSortDemo [2; 5; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem488 : bubbleSortDemo [2; 5; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem489 : bubbleSortDemo [2; 5; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem490 : bubbleSortDemo [2; 5; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem491 : bubbleSortDemo [2; 5; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem492 : bubbleSortDemo [2; 5; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem493 : bubbleSortDemo [2; 5; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem494 : bubbleSortDemo [2; 5; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem495 : bubbleSortDemo [2; 5; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem496 : bubbleSortDemo [2; 5; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem497 : bubbleSortDemo [2; 5; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem498 : bubbleSortDemo [2; 5; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem499 : bubbleSortDemo [2; 5; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem500 : bubbleSortDemo [2; 5; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem501 : bubbleSortDemo [2; 5; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem502 : bubbleSortDemo [2; 5; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem503 : bubbleSortDemo [2; 5; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem504 : bubbleSortDemo [2; 5; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem505 : bubbleSortDemo [2; 5; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem506 : bubbleSortDemo [2; 5; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem507 : bubbleSortDemo [2; 5; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem508 : bubbleSortDemo [2; 5; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem509 : bubbleSortDemo [2; 5; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem510 : bubbleSortDemo [3; 0; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem511 : bubbleSortDemo [3; 0; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem512 : bubbleSortDemo [3; 0; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem513 : bubbleSortDemo [3; 0; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem514 : bubbleSortDemo [3; 0; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem515 : bubbleSortDemo [3; 0; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem516 : bubbleSortDemo [3; 0; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem517 : bubbleSortDemo [3; 0; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem518 : bubbleSortDemo [3; 0; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem519 : bubbleSortDemo [3; 0; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem520 : bubbleSortDemo [3; 0; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem521 : bubbleSortDemo [3; 0; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem522 : bubbleSortDemo [3; 0; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem523 : bubbleSortDemo [3; 0; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem524 : bubbleSortDemo [3; 0; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem525 : bubbleSortDemo [3; 0; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem526 : bubbleSortDemo [3; 0; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem527 : bubbleSortDemo [3; 0; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem528 : bubbleSortDemo [3; 0; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem529 : bubbleSortDemo [3; 0; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem530 : bubbleSortDemo [3; 0; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem531 : bubbleSortDemo [3; 0; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem532 : bubbleSortDemo [3; 0; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem533 : bubbleSortDemo [3; 0; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem534 : bubbleSortDemo [3; 1; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem535 : bubbleSortDemo [3; 1; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem536 : bubbleSortDemo [3; 1; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem537 : bubbleSortDemo [3; 1; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem538 : bubbleSortDemo [3; 1; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem539 : bubbleSortDemo [3; 1; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem540 : bubbleSortDemo [3; 1; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem541 : bubbleSortDemo [3; 1; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem542 : bubbleSortDemo [3; 1; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem543 : bubbleSortDemo [3; 1; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem544 : bubbleSortDemo [3; 1; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem545 : bubbleSortDemo [3; 1; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem546 : bubbleSortDemo [3; 1; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem547 : bubbleSortDemo [3; 1; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem548 : bubbleSortDemo [3; 1; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem549 : bubbleSortDemo [3; 1; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem550 : bubbleSortDemo [3; 1; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem551 : bubbleSortDemo [3; 1; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem552 : bubbleSortDemo [3; 1; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem553 : bubbleSortDemo [3; 1; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem554 : bubbleSortDemo [3; 1; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem555 : bubbleSortDemo [3; 1; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem556 : bubbleSortDemo [3; 1; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem557 : bubbleSortDemo [3; 1; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem558 : bubbleSortDemo [3; 2; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem559 : bubbleSortDemo [3; 2; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem560 : bubbleSortDemo [3; 2; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem561 : bubbleSortDemo [3; 2; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem562 : bubbleSortDemo [3; 2; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem563 : bubbleSortDemo [3; 2; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem564 : bubbleSortDemo [3; 2; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem565 : bubbleSortDemo [3; 2; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem566 : bubbleSortDemo [3; 2; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem567 : bubbleSortDemo [3; 2; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem568 : bubbleSortDemo [3; 2; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem569 : bubbleSortDemo [3; 2; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem570 : bubbleSortDemo [3; 2; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem571 : bubbleSortDemo [3; 2; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem572 : bubbleSortDemo [3; 2; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem573 : bubbleSortDemo [3; 2; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem574 : bubbleSortDemo [3; 2; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem575 : bubbleSortDemo [3; 2; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem576 : bubbleSortDemo [3; 2; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem577 : bubbleSortDemo [3; 2; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem578 : bubbleSortDemo [3; 2; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem579 : bubbleSortDemo [3; 2; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem580 : bubbleSortDemo [3; 2; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem581 : bubbleSortDemo [3; 2; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem582 : bubbleSortDemo [3; 4; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem583 : bubbleSortDemo [3; 4; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem584 : bubbleSortDemo [3; 4; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem585 : bubbleSortDemo [3; 4; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem586 : bubbleSortDemo [3; 4; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem587 : bubbleSortDemo [3; 4; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem588 : bubbleSortDemo [3; 4; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem589 : bubbleSortDemo [3; 4; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem590 : bubbleSortDemo [3; 4; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem591 : bubbleSortDemo [3; 4; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem592 : bubbleSortDemo [3; 4; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem593 : bubbleSortDemo [3; 4; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem594 : bubbleSortDemo [3; 4; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem595 : bubbleSortDemo [3; 4; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem596 : bubbleSortDemo [3; 4; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem597 : bubbleSortDemo [3; 4; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem598 : bubbleSortDemo [3; 4; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem599 : bubbleSortDemo [3; 4; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem600 : bubbleSortDemo [3; 4; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem601 : bubbleSortDemo [3; 4; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem602 : bubbleSortDemo [3; 4; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem603 : bubbleSortDemo [3; 4; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem604 : bubbleSortDemo [3; 4; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem605 : bubbleSortDemo [3; 4; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem606 : bubbleSortDemo [3; 5; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem607 : bubbleSortDemo [3; 5; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem608 : bubbleSortDemo [3; 5; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem609 : bubbleSortDemo [3; 5; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem610 : bubbleSortDemo [3; 5; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem611 : bubbleSortDemo [3; 5; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem612 : bubbleSortDemo [3; 5; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem613 : bubbleSortDemo [3; 5; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem614 : bubbleSortDemo [3; 5; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem615 : bubbleSortDemo [3; 5; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem616 : bubbleSortDemo [3; 5; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem617 : bubbleSortDemo [3; 5; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem618 : bubbleSortDemo [3; 5; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem619 : bubbleSortDemo [3; 5; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem620 : bubbleSortDemo [3; 5; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem621 : bubbleSortDemo [3; 5; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem622 : bubbleSortDemo [3; 5; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem623 : bubbleSortDemo [3; 5; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem624 : bubbleSortDemo [3; 5; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem625 : bubbleSortDemo [3; 5; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem626 : bubbleSortDemo [3; 5; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem627 : bubbleSortDemo [3; 5; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem628 : bubbleSortDemo [3; 5; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem629 : bubbleSortDemo [3; 5; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem630 : bubbleSortDemo [4; 0; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem631 : bubbleSortDemo [4; 0; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem632 : bubbleSortDemo [4; 0; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem633 : bubbleSortDemo [4; 0; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem634 : bubbleSortDemo [4; 0; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem635 : bubbleSortDemo [4; 0; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem636 : bubbleSortDemo [4; 0; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem637 : bubbleSortDemo [4; 0; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem638 : bubbleSortDemo [4; 0; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem639 : bubbleSortDemo [4; 0; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem640 : bubbleSortDemo [4; 0; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem641 : bubbleSortDemo [4; 0; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem642 : bubbleSortDemo [4; 0; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem643 : bubbleSortDemo [4; 0; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem644 : bubbleSortDemo [4; 0; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem645 : bubbleSortDemo [4; 0; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem646 : bubbleSortDemo [4; 0; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem647 : bubbleSortDemo [4; 0; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem648 : bubbleSortDemo [4; 0; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem649 : bubbleSortDemo [4; 0; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem650 : bubbleSortDemo [4; 0; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem651 : bubbleSortDemo [4; 0; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem652 : bubbleSortDemo [4; 0; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem653 : bubbleSortDemo [4; 0; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem654 : bubbleSortDemo [4; 1; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem655 : bubbleSortDemo [4; 1; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem656 : bubbleSortDemo [4; 1; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem657 : bubbleSortDemo [4; 1; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem658 : bubbleSortDemo [4; 1; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem659 : bubbleSortDemo [4; 1; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem660 : bubbleSortDemo [4; 1; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem661 : bubbleSortDemo [4; 1; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem662 : bubbleSortDemo [4; 1; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem663 : bubbleSortDemo [4; 1; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem664 : bubbleSortDemo [4; 1; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem665 : bubbleSortDemo [4; 1; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem666 : bubbleSortDemo [4; 1; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem667 : bubbleSortDemo [4; 1; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem668 : bubbleSortDemo [4; 1; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem669 : bubbleSortDemo [4; 1; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem670 : bubbleSortDemo [4; 1; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem671 : bubbleSortDemo [4; 1; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem672 : bubbleSortDemo [4; 1; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem673 : bubbleSortDemo [4; 1; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem674 : bubbleSortDemo [4; 1; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem675 : bubbleSortDemo [4; 1; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem676 : bubbleSortDemo [4; 1; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem677 : bubbleSortDemo [4; 1; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem678 : bubbleSortDemo [4; 2; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem679 : bubbleSortDemo [4; 2; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem680 : bubbleSortDemo [4; 2; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem681 : bubbleSortDemo [4; 2; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem682 : bubbleSortDemo [4; 2; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem683 : bubbleSortDemo [4; 2; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem684 : bubbleSortDemo [4; 2; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem685 : bubbleSortDemo [4; 2; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem686 : bubbleSortDemo [4; 2; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem687 : bubbleSortDemo [4; 2; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem688 : bubbleSortDemo [4; 2; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem689 : bubbleSortDemo [4; 2; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem690 : bubbleSortDemo [4; 2; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem691 : bubbleSortDemo [4; 2; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem692 : bubbleSortDemo [4; 2; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem693 : bubbleSortDemo [4; 2; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem694 : bubbleSortDemo [4; 2; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem695 : bubbleSortDemo [4; 2; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem696 : bubbleSortDemo [4; 2; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem697 : bubbleSortDemo [4; 2; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem698 : bubbleSortDemo [4; 2; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem699 : bubbleSortDemo [4; 2; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem700 : bubbleSortDemo [4; 2; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem701 : bubbleSortDemo [4; 2; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem702 : bubbleSortDemo [4; 3; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem703 : bubbleSortDemo [4; 3; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem704 : bubbleSortDemo [4; 3; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem705 : bubbleSortDemo [4; 3; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem706 : bubbleSortDemo [4; 3; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem707 : bubbleSortDemo [4; 3; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem708 : bubbleSortDemo [4; 3; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem709 : bubbleSortDemo [4; 3; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem710 : bubbleSortDemo [4; 3; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem711 : bubbleSortDemo [4; 3; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem712 : bubbleSortDemo [4; 3; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem713 : bubbleSortDemo [4; 3; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem714 : bubbleSortDemo [4; 3; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem715 : bubbleSortDemo [4; 3; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem716 : bubbleSortDemo [4; 3; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem717 : bubbleSortDemo [4; 3; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem718 : bubbleSortDemo [4; 3; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem719 : bubbleSortDemo [4; 3; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem720 : bubbleSortDemo [4; 3; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem721 : bubbleSortDemo [4; 3; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem722 : bubbleSortDemo [4; 3; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem723 : bubbleSortDemo [4; 3; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem724 : bubbleSortDemo [4; 3; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem725 : bubbleSortDemo [4; 3; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem726 : bubbleSortDemo [4; 5; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem727 : bubbleSortDemo [4; 5; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem728 : bubbleSortDemo [4; 5; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem729 : bubbleSortDemo [4; 5; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem730 : bubbleSortDemo [4; 5; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem731 : bubbleSortDemo [4; 5; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem732 : bubbleSortDemo [4; 5; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem733 : bubbleSortDemo [4; 5; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem734 : bubbleSortDemo [4; 5; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem735 : bubbleSortDemo [4; 5; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem736 : bubbleSortDemo [4; 5; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem737 : bubbleSortDemo [4; 5; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem738 : bubbleSortDemo [4; 5; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem739 : bubbleSortDemo [4; 5; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem740 : bubbleSortDemo [4; 5; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem741 : bubbleSortDemo [4; 5; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem742 : bubbleSortDemo [4; 5; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem743 : bubbleSortDemo [4; 5; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem744 : bubbleSortDemo [4; 5; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem745 : bubbleSortDemo [4; 5; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem746 : bubbleSortDemo [4; 5; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem747 : bubbleSortDemo [4; 5; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem748 : bubbleSortDemo [4; 5; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem749 : bubbleSortDemo [4; 5; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem750 : bubbleSortDemo [5; 0; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem751 : bubbleSortDemo [5; 0; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem752 : bubbleSortDemo [5; 0; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem753 : bubbleSortDemo [5; 0; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem754 : bubbleSortDemo [5; 0; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem755 : bubbleSortDemo [5; 0; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem756 : bubbleSortDemo [5; 0; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem757 : bubbleSortDemo [5; 0; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem758 : bubbleSortDemo [5; 0; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem759 : bubbleSortDemo [5; 0; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem760 : bubbleSortDemo [5; 0; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem761 : bubbleSortDemo [5; 0; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem762 : bubbleSortDemo [5; 0; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem763 : bubbleSortDemo [5; 0; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem764 : bubbleSortDemo [5; 0; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem765 : bubbleSortDemo [5; 0; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem766 : bubbleSortDemo [5; 0; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem767 : bubbleSortDemo [5; 0; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem768 : bubbleSortDemo [5; 0; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem769 : bubbleSortDemo [5; 0; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem770 : bubbleSortDemo [5; 0; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem771 : bubbleSortDemo [5; 0; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem772 : bubbleSortDemo [5; 0; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem773 : bubbleSortDemo [5; 0; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem774 : bubbleSortDemo [5; 1; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem775 : bubbleSortDemo [5; 1; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem776 : bubbleSortDemo [5; 1; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem777 : bubbleSortDemo [5; 1; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem778 : bubbleSortDemo [5; 1; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem779 : bubbleSortDemo [5; 1; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem780 : bubbleSortDemo [5; 1; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem781 : bubbleSortDemo [5; 1; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem782 : bubbleSortDemo [5; 1; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem783 : bubbleSortDemo [5; 1; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem784 : bubbleSortDemo [5; 1; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem785 : bubbleSortDemo [5; 1; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem786 : bubbleSortDemo [5; 1; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem787 : bubbleSortDemo [5; 1; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem788 : bubbleSortDemo [5; 1; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem789 : bubbleSortDemo [5; 1; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem790 : bubbleSortDemo [5; 1; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem791 : bubbleSortDemo [5; 1; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem792 : bubbleSortDemo [5; 1; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem793 : bubbleSortDemo [5; 1; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem794 : bubbleSortDemo [5; 1; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem795 : bubbleSortDemo [5; 1; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem796 : bubbleSortDemo [5; 1; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem797 : bubbleSortDemo [5; 1; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem798 : bubbleSortDemo [5; 2; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem799 : bubbleSortDemo [5; 2; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem800 : bubbleSortDemo [5; 2; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem801 : bubbleSortDemo [5; 2; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem802 : bubbleSortDemo [5; 2; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem803 : bubbleSortDemo [5; 2; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem804 : bubbleSortDemo [5; 2; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem805 : bubbleSortDemo [5; 2; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem806 : bubbleSortDemo [5; 2; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem807 : bubbleSortDemo [5; 2; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem808 : bubbleSortDemo [5; 2; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem809 : bubbleSortDemo [5; 2; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem810 : bubbleSortDemo [5; 2; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem811 : bubbleSortDemo [5; 2; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem812 : bubbleSortDemo [5; 2; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem813 : bubbleSortDemo [5; 2; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem814 : bubbleSortDemo [5; 2; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem815 : bubbleSortDemo [5; 2; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem816 : bubbleSortDemo [5; 2; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem817 : bubbleSortDemo [5; 2; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem818 : bubbleSortDemo [5; 2; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem819 : bubbleSortDemo [5; 2; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem820 : bubbleSortDemo [5; 2; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem821 : bubbleSortDemo [5; 2; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem822 : bubbleSortDemo [5; 3; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem823 : bubbleSortDemo [5; 3; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem824 : bubbleSortDemo [5; 3; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem825 : bubbleSortDemo [5; 3; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem826 : bubbleSortDemo [5; 3; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem827 : bubbleSortDemo [5; 3; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem828 : bubbleSortDemo [5; 3; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem829 : bubbleSortDemo [5; 3; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem830 : bubbleSortDemo [5; 3; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem831 : bubbleSortDemo [5; 3; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem832 : bubbleSortDemo [5; 3; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem833 : bubbleSortDemo [5; 3; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem834 : bubbleSortDemo [5; 3; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem835 : bubbleSortDemo [5; 3; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem836 : bubbleSortDemo [5; 3; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem837 : bubbleSortDemo [5; 3; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem838 : bubbleSortDemo [5; 3; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem839 : bubbleSortDemo [5; 3; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem840 : bubbleSortDemo [5; 3; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem841 : bubbleSortDemo [5; 3; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem842 : bubbleSortDemo [5; 3; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem843 : bubbleSortDemo [5; 3; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem844 : bubbleSortDemo [5; 3; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem845 : bubbleSortDemo [5; 3; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem846 : bubbleSortDemo [5; 4; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem847 : bubbleSortDemo [5; 4; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem848 : bubbleSortDemo [5; 4; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem849 : bubbleSortDemo [5; 4; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem850 : bubbleSortDemo [5; 4; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem851 : bubbleSortDemo [5; 4; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem852 : bubbleSortDemo [5; 4; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem853 : bubbleSortDemo [5; 4; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem854 : bubbleSortDemo [5; 4; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem855 : bubbleSortDemo [5; 4; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem856 : bubbleSortDemo [5; 4; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem857 : bubbleSortDemo [5; 4; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem858 : bubbleSortDemo [5; 4; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem859 : bubbleSortDemo [5; 4; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem860 : bubbleSortDemo [5; 4; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem861 : bubbleSortDemo [5; 4; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem862 : bubbleSortDemo [5; 4; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem863 : bubbleSortDemo [5; 4; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem864 : bubbleSortDemo [5; 4; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem865 : bubbleSortDemo [5; 4; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem866 : bubbleSortDemo [5; 4; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem867 : bubbleSortDemo [5; 4; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem868 : bubbleSortDemo [5; 4; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestTheorem869 : bubbleSortDemo [5; 4; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

