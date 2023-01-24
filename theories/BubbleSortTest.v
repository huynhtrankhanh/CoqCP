From stdpp Require Import numbers list.
From CoqCP Require Import PropertyPreservedAfterSorting.

Lemma bubbleSortTestLemma0 : bubbleSortDemo [0; 1; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma1 : bubbleSortDemo [0; 2; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma2 : bubbleSortDemo [1; 0; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma3 : bubbleSortDemo [1; 2; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma4 : bubbleSortDemo [2; 0; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma5 : bubbleSortDemo [2; 1; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma6 : bubbleSortDemo [0; 1; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma7 : bubbleSortDemo [0; 1; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma8 : bubbleSortDemo [0; 2; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma9 : bubbleSortDemo [0; 2; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma10 : bubbleSortDemo [0; 3; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma11 : bubbleSortDemo [0; 3; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma12 : bubbleSortDemo [1; 0; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma13 : bubbleSortDemo [1; 0; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma14 : bubbleSortDemo [1; 2; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma15 : bubbleSortDemo [1; 2; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma16 : bubbleSortDemo [1; 3; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma17 : bubbleSortDemo [1; 3; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma18 : bubbleSortDemo [2; 0; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma19 : bubbleSortDemo [2; 0; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma20 : bubbleSortDemo [2; 1; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma21 : bubbleSortDemo [2; 1; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma22 : bubbleSortDemo [2; 3; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma23 : bubbleSortDemo [2; 3; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma24 : bubbleSortDemo [3; 0; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma25 : bubbleSortDemo [3; 0; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma26 : bubbleSortDemo [3; 1; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma27 : bubbleSortDemo [3; 1; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma28 : bubbleSortDemo [3; 2; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma29 : bubbleSortDemo [3; 2; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma30 : bubbleSortDemo [0; 1; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma31 : bubbleSortDemo [0; 1; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma32 : bubbleSortDemo [0; 1; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma33 : bubbleSortDemo [0; 1; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma34 : bubbleSortDemo [0; 1; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma35 : bubbleSortDemo [0; 1; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma36 : bubbleSortDemo [0; 2; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma37 : bubbleSortDemo [0; 2; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma38 : bubbleSortDemo [0; 2; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma39 : bubbleSortDemo [0; 2; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma40 : bubbleSortDemo [0; 2; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma41 : bubbleSortDemo [0; 2; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma42 : bubbleSortDemo [0; 3; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma43 : bubbleSortDemo [0; 3; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma44 : bubbleSortDemo [0; 3; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma45 : bubbleSortDemo [0; 3; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma46 : bubbleSortDemo [0; 3; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma47 : bubbleSortDemo [0; 3; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma48 : bubbleSortDemo [0; 4; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma49 : bubbleSortDemo [0; 4; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma50 : bubbleSortDemo [0; 4; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma51 : bubbleSortDemo [0; 4; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma52 : bubbleSortDemo [0; 4; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma53 : bubbleSortDemo [0; 4; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma54 : bubbleSortDemo [1; 0; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma55 : bubbleSortDemo [1; 0; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma56 : bubbleSortDemo [1; 0; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma57 : bubbleSortDemo [1; 0; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma58 : bubbleSortDemo [1; 0; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma59 : bubbleSortDemo [1; 0; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma60 : bubbleSortDemo [1; 2; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma61 : bubbleSortDemo [1; 2; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma62 : bubbleSortDemo [1; 2; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma63 : bubbleSortDemo [1; 2; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma64 : bubbleSortDemo [1; 2; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma65 : bubbleSortDemo [1; 2; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma66 : bubbleSortDemo [1; 3; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma67 : bubbleSortDemo [1; 3; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma68 : bubbleSortDemo [1; 3; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma69 : bubbleSortDemo [1; 3; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma70 : bubbleSortDemo [1; 3; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma71 : bubbleSortDemo [1; 3; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma72 : bubbleSortDemo [1; 4; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma73 : bubbleSortDemo [1; 4; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma74 : bubbleSortDemo [1; 4; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma75 : bubbleSortDemo [1; 4; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma76 : bubbleSortDemo [1; 4; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma77 : bubbleSortDemo [1; 4; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma78 : bubbleSortDemo [2; 0; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma79 : bubbleSortDemo [2; 0; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma80 : bubbleSortDemo [2; 0; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma81 : bubbleSortDemo [2; 0; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma82 : bubbleSortDemo [2; 0; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma83 : bubbleSortDemo [2; 0; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma84 : bubbleSortDemo [2; 1; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma85 : bubbleSortDemo [2; 1; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma86 : bubbleSortDemo [2; 1; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma87 : bubbleSortDemo [2; 1; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma88 : bubbleSortDemo [2; 1; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma89 : bubbleSortDemo [2; 1; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma90 : bubbleSortDemo [2; 3; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma91 : bubbleSortDemo [2; 3; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma92 : bubbleSortDemo [2; 3; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma93 : bubbleSortDemo [2; 3; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma94 : bubbleSortDemo [2; 3; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma95 : bubbleSortDemo [2; 3; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma96 : bubbleSortDemo [2; 4; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma97 : bubbleSortDemo [2; 4; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma98 : bubbleSortDemo [2; 4; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma99 : bubbleSortDemo [2; 4; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma100 : bubbleSortDemo [2; 4; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma101 : bubbleSortDemo [2; 4; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma102 : bubbleSortDemo [3; 0; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma103 : bubbleSortDemo [3; 0; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma104 : bubbleSortDemo [3; 0; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma105 : bubbleSortDemo [3; 0; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma106 : bubbleSortDemo [3; 0; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma107 : bubbleSortDemo [3; 0; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma108 : bubbleSortDemo [3; 1; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma109 : bubbleSortDemo [3; 1; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma110 : bubbleSortDemo [3; 1; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma111 : bubbleSortDemo [3; 1; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma112 : bubbleSortDemo [3; 1; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma113 : bubbleSortDemo [3; 1; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma114 : bubbleSortDemo [3; 2; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma115 : bubbleSortDemo [3; 2; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma116 : bubbleSortDemo [3; 2; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma117 : bubbleSortDemo [3; 2; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma118 : bubbleSortDemo [3; 2; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma119 : bubbleSortDemo [3; 2; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma120 : bubbleSortDemo [3; 4; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma121 : bubbleSortDemo [3; 4; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma122 : bubbleSortDemo [3; 4; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma123 : bubbleSortDemo [3; 4; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma124 : bubbleSortDemo [3; 4; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma125 : bubbleSortDemo [3; 4; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma126 : bubbleSortDemo [4; 0; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma127 : bubbleSortDemo [4; 0; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma128 : bubbleSortDemo [4; 0; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma129 : bubbleSortDemo [4; 0; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma130 : bubbleSortDemo [4; 0; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma131 : bubbleSortDemo [4; 0; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma132 : bubbleSortDemo [4; 1; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma133 : bubbleSortDemo [4; 1; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma134 : bubbleSortDemo [4; 1; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma135 : bubbleSortDemo [4; 1; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma136 : bubbleSortDemo [4; 1; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma137 : bubbleSortDemo [4; 1; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma138 : bubbleSortDemo [4; 2; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma139 : bubbleSortDemo [4; 2; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma140 : bubbleSortDemo [4; 2; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma141 : bubbleSortDemo [4; 2; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma142 : bubbleSortDemo [4; 2; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma143 : bubbleSortDemo [4; 2; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma144 : bubbleSortDemo [4; 3; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma145 : bubbleSortDemo [4; 3; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma146 : bubbleSortDemo [4; 3; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma147 : bubbleSortDemo [4; 3; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma148 : bubbleSortDemo [4; 3; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma149 : bubbleSortDemo [4; 3; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma150 : bubbleSortDemo [0; 1; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma151 : bubbleSortDemo [0; 1; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma152 : bubbleSortDemo [0; 1; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma153 : bubbleSortDemo [0; 1; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma154 : bubbleSortDemo [0; 1; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma155 : bubbleSortDemo [0; 1; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma156 : bubbleSortDemo [0; 1; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma157 : bubbleSortDemo [0; 1; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma158 : bubbleSortDemo [0; 1; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma159 : bubbleSortDemo [0; 1; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma160 : bubbleSortDemo [0; 1; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma161 : bubbleSortDemo [0; 1; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma162 : bubbleSortDemo [0; 1; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma163 : bubbleSortDemo [0; 1; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma164 : bubbleSortDemo [0; 1; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma165 : bubbleSortDemo [0; 1; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma166 : bubbleSortDemo [0; 1; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma167 : bubbleSortDemo [0; 1; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma168 : bubbleSortDemo [0; 1; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma169 : bubbleSortDemo [0; 1; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma170 : bubbleSortDemo [0; 1; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma171 : bubbleSortDemo [0; 1; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma172 : bubbleSortDemo [0; 1; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma173 : bubbleSortDemo [0; 1; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma174 : bubbleSortDemo [0; 2; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma175 : bubbleSortDemo [0; 2; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma176 : bubbleSortDemo [0; 2; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma177 : bubbleSortDemo [0; 2; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma178 : bubbleSortDemo [0; 2; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma179 : bubbleSortDemo [0; 2; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma180 : bubbleSortDemo [0; 2; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma181 : bubbleSortDemo [0; 2; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma182 : bubbleSortDemo [0; 2; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma183 : bubbleSortDemo [0; 2; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma184 : bubbleSortDemo [0; 2; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma185 : bubbleSortDemo [0; 2; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma186 : bubbleSortDemo [0; 2; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma187 : bubbleSortDemo [0; 2; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma188 : bubbleSortDemo [0; 2; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma189 : bubbleSortDemo [0; 2; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma190 : bubbleSortDemo [0; 2; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma191 : bubbleSortDemo [0; 2; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma192 : bubbleSortDemo [0; 2; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma193 : bubbleSortDemo [0; 2; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma194 : bubbleSortDemo [0; 2; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma195 : bubbleSortDemo [0; 2; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma196 : bubbleSortDemo [0; 2; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma197 : bubbleSortDemo [0; 2; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma198 : bubbleSortDemo [0; 3; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma199 : bubbleSortDemo [0; 3; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma200 : bubbleSortDemo [0; 3; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma201 : bubbleSortDemo [0; 3; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma202 : bubbleSortDemo [0; 3; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma203 : bubbleSortDemo [0; 3; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma204 : bubbleSortDemo [0; 3; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma205 : bubbleSortDemo [0; 3; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma206 : bubbleSortDemo [0; 3; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma207 : bubbleSortDemo [0; 3; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma208 : bubbleSortDemo [0; 3; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma209 : bubbleSortDemo [0; 3; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma210 : bubbleSortDemo [0; 3; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma211 : bubbleSortDemo [0; 3; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma212 : bubbleSortDemo [0; 3; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma213 : bubbleSortDemo [0; 3; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma214 : bubbleSortDemo [0; 3; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma215 : bubbleSortDemo [0; 3; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma216 : bubbleSortDemo [0; 3; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma217 : bubbleSortDemo [0; 3; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma218 : bubbleSortDemo [0; 3; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma219 : bubbleSortDemo [0; 3; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma220 : bubbleSortDemo [0; 3; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma221 : bubbleSortDemo [0; 3; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma222 : bubbleSortDemo [0; 4; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma223 : bubbleSortDemo [0; 4; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma224 : bubbleSortDemo [0; 4; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma225 : bubbleSortDemo [0; 4; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma226 : bubbleSortDemo [0; 4; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma227 : bubbleSortDemo [0; 4; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma228 : bubbleSortDemo [0; 4; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma229 : bubbleSortDemo [0; 4; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma230 : bubbleSortDemo [0; 4; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma231 : bubbleSortDemo [0; 4; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma232 : bubbleSortDemo [0; 4; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma233 : bubbleSortDemo [0; 4; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma234 : bubbleSortDemo [0; 4; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma235 : bubbleSortDemo [0; 4; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma236 : bubbleSortDemo [0; 4; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma237 : bubbleSortDemo [0; 4; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma238 : bubbleSortDemo [0; 4; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma239 : bubbleSortDemo [0; 4; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma240 : bubbleSortDemo [0; 4; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma241 : bubbleSortDemo [0; 4; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma242 : bubbleSortDemo [0; 4; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma243 : bubbleSortDemo [0; 4; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma244 : bubbleSortDemo [0; 4; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma245 : bubbleSortDemo [0; 4; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma246 : bubbleSortDemo [0; 5; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma247 : bubbleSortDemo [0; 5; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma248 : bubbleSortDemo [0; 5; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma249 : bubbleSortDemo [0; 5; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma250 : bubbleSortDemo [0; 5; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma251 : bubbleSortDemo [0; 5; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma252 : bubbleSortDemo [0; 5; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma253 : bubbleSortDemo [0; 5; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma254 : bubbleSortDemo [0; 5; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma255 : bubbleSortDemo [0; 5; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma256 : bubbleSortDemo [0; 5; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma257 : bubbleSortDemo [0; 5; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma258 : bubbleSortDemo [0; 5; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma259 : bubbleSortDemo [0; 5; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma260 : bubbleSortDemo [0; 5; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma261 : bubbleSortDemo [0; 5; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma262 : bubbleSortDemo [0; 5; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma263 : bubbleSortDemo [0; 5; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma264 : bubbleSortDemo [0; 5; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma265 : bubbleSortDemo [0; 5; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma266 : bubbleSortDemo [0; 5; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma267 : bubbleSortDemo [0; 5; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma268 : bubbleSortDemo [0; 5; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma269 : bubbleSortDemo [0; 5; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma270 : bubbleSortDemo [1; 0; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma271 : bubbleSortDemo [1; 0; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma272 : bubbleSortDemo [1; 0; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma273 : bubbleSortDemo [1; 0; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma274 : bubbleSortDemo [1; 0; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma275 : bubbleSortDemo [1; 0; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma276 : bubbleSortDemo [1; 0; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma277 : bubbleSortDemo [1; 0; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma278 : bubbleSortDemo [1; 0; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma279 : bubbleSortDemo [1; 0; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma280 : bubbleSortDemo [1; 0; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma281 : bubbleSortDemo [1; 0; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma282 : bubbleSortDemo [1; 0; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma283 : bubbleSortDemo [1; 0; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma284 : bubbleSortDemo [1; 0; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma285 : bubbleSortDemo [1; 0; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma286 : bubbleSortDemo [1; 0; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma287 : bubbleSortDemo [1; 0; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma288 : bubbleSortDemo [1; 0; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma289 : bubbleSortDemo [1; 0; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma290 : bubbleSortDemo [1; 0; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma291 : bubbleSortDemo [1; 0; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma292 : bubbleSortDemo [1; 0; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma293 : bubbleSortDemo [1; 0; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma294 : bubbleSortDemo [1; 2; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma295 : bubbleSortDemo [1; 2; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma296 : bubbleSortDemo [1; 2; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma297 : bubbleSortDemo [1; 2; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma298 : bubbleSortDemo [1; 2; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma299 : bubbleSortDemo [1; 2; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma300 : bubbleSortDemo [1; 2; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma301 : bubbleSortDemo [1; 2; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma302 : bubbleSortDemo [1; 2; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma303 : bubbleSortDemo [1; 2; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma304 : bubbleSortDemo [1; 2; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma305 : bubbleSortDemo [1; 2; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma306 : bubbleSortDemo [1; 2; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma307 : bubbleSortDemo [1; 2; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma308 : bubbleSortDemo [1; 2; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma309 : bubbleSortDemo [1; 2; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma310 : bubbleSortDemo [1; 2; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma311 : bubbleSortDemo [1; 2; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma312 : bubbleSortDemo [1; 2; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma313 : bubbleSortDemo [1; 2; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma314 : bubbleSortDemo [1; 2; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma315 : bubbleSortDemo [1; 2; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma316 : bubbleSortDemo [1; 2; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma317 : bubbleSortDemo [1; 2; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma318 : bubbleSortDemo [1; 3; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma319 : bubbleSortDemo [1; 3; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma320 : bubbleSortDemo [1; 3; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma321 : bubbleSortDemo [1; 3; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma322 : bubbleSortDemo [1; 3; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma323 : bubbleSortDemo [1; 3; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma324 : bubbleSortDemo [1; 3; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma325 : bubbleSortDemo [1; 3; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma326 : bubbleSortDemo [1; 3; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma327 : bubbleSortDemo [1; 3; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma328 : bubbleSortDemo [1; 3; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma329 : bubbleSortDemo [1; 3; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma330 : bubbleSortDemo [1; 3; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma331 : bubbleSortDemo [1; 3; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma332 : bubbleSortDemo [1; 3; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma333 : bubbleSortDemo [1; 3; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma334 : bubbleSortDemo [1; 3; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma335 : bubbleSortDemo [1; 3; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma336 : bubbleSortDemo [1; 3; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma337 : bubbleSortDemo [1; 3; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma338 : bubbleSortDemo [1; 3; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma339 : bubbleSortDemo [1; 3; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma340 : bubbleSortDemo [1; 3; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma341 : bubbleSortDemo [1; 3; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma342 : bubbleSortDemo [1; 4; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma343 : bubbleSortDemo [1; 4; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma344 : bubbleSortDemo [1; 4; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma345 : bubbleSortDemo [1; 4; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma346 : bubbleSortDemo [1; 4; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma347 : bubbleSortDemo [1; 4; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma348 : bubbleSortDemo [1; 4; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma349 : bubbleSortDemo [1; 4; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma350 : bubbleSortDemo [1; 4; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma351 : bubbleSortDemo [1; 4; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma352 : bubbleSortDemo [1; 4; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma353 : bubbleSortDemo [1; 4; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma354 : bubbleSortDemo [1; 4; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma355 : bubbleSortDemo [1; 4; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma356 : bubbleSortDemo [1; 4; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma357 : bubbleSortDemo [1; 4; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma358 : bubbleSortDemo [1; 4; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma359 : bubbleSortDemo [1; 4; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma360 : bubbleSortDemo [1; 4; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma361 : bubbleSortDemo [1; 4; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma362 : bubbleSortDemo [1; 4; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma363 : bubbleSortDemo [1; 4; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma364 : bubbleSortDemo [1; 4; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma365 : bubbleSortDemo [1; 4; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma366 : bubbleSortDemo [1; 5; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma367 : bubbleSortDemo [1; 5; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma368 : bubbleSortDemo [1; 5; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma369 : bubbleSortDemo [1; 5; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma370 : bubbleSortDemo [1; 5; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma371 : bubbleSortDemo [1; 5; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma372 : bubbleSortDemo [1; 5; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma373 : bubbleSortDemo [1; 5; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma374 : bubbleSortDemo [1; 5; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma375 : bubbleSortDemo [1; 5; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma376 : bubbleSortDemo [1; 5; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma377 : bubbleSortDemo [1; 5; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma378 : bubbleSortDemo [1; 5; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma379 : bubbleSortDemo [1; 5; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma380 : bubbleSortDemo [1; 5; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma381 : bubbleSortDemo [1; 5; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma382 : bubbleSortDemo [1; 5; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma383 : bubbleSortDemo [1; 5; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma384 : bubbleSortDemo [1; 5; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma385 : bubbleSortDemo [1; 5; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma386 : bubbleSortDemo [1; 5; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma387 : bubbleSortDemo [1; 5; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma388 : bubbleSortDemo [1; 5; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma389 : bubbleSortDemo [1; 5; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma390 : bubbleSortDemo [2; 0; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma391 : bubbleSortDemo [2; 0; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma392 : bubbleSortDemo [2; 0; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma393 : bubbleSortDemo [2; 0; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma394 : bubbleSortDemo [2; 0; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma395 : bubbleSortDemo [2; 0; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma396 : bubbleSortDemo [2; 0; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma397 : bubbleSortDemo [2; 0; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma398 : bubbleSortDemo [2; 0; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma399 : bubbleSortDemo [2; 0; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma400 : bubbleSortDemo [2; 0; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma401 : bubbleSortDemo [2; 0; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma402 : bubbleSortDemo [2; 0; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma403 : bubbleSortDemo [2; 0; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma404 : bubbleSortDemo [2; 0; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma405 : bubbleSortDemo [2; 0; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma406 : bubbleSortDemo [2; 0; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma407 : bubbleSortDemo [2; 0; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma408 : bubbleSortDemo [2; 0; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma409 : bubbleSortDemo [2; 0; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma410 : bubbleSortDemo [2; 0; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma411 : bubbleSortDemo [2; 0; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma412 : bubbleSortDemo [2; 0; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma413 : bubbleSortDemo [2; 0; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma414 : bubbleSortDemo [2; 1; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma415 : bubbleSortDemo [2; 1; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma416 : bubbleSortDemo [2; 1; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma417 : bubbleSortDemo [2; 1; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma418 : bubbleSortDemo [2; 1; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma419 : bubbleSortDemo [2; 1; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma420 : bubbleSortDemo [2; 1; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma421 : bubbleSortDemo [2; 1; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma422 : bubbleSortDemo [2; 1; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma423 : bubbleSortDemo [2; 1; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma424 : bubbleSortDemo [2; 1; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma425 : bubbleSortDemo [2; 1; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma426 : bubbleSortDemo [2; 1; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma427 : bubbleSortDemo [2; 1; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma428 : bubbleSortDemo [2; 1; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma429 : bubbleSortDemo [2; 1; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma430 : bubbleSortDemo [2; 1; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma431 : bubbleSortDemo [2; 1; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma432 : bubbleSortDemo [2; 1; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma433 : bubbleSortDemo [2; 1; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma434 : bubbleSortDemo [2; 1; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma435 : bubbleSortDemo [2; 1; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma436 : bubbleSortDemo [2; 1; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma437 : bubbleSortDemo [2; 1; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma438 : bubbleSortDemo [2; 3; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma439 : bubbleSortDemo [2; 3; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma440 : bubbleSortDemo [2; 3; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma441 : bubbleSortDemo [2; 3; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma442 : bubbleSortDemo [2; 3; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma443 : bubbleSortDemo [2; 3; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma444 : bubbleSortDemo [2; 3; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma445 : bubbleSortDemo [2; 3; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma446 : bubbleSortDemo [2; 3; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma447 : bubbleSortDemo [2; 3; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma448 : bubbleSortDemo [2; 3; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma449 : bubbleSortDemo [2; 3; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma450 : bubbleSortDemo [2; 3; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma451 : bubbleSortDemo [2; 3; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma452 : bubbleSortDemo [2; 3; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma453 : bubbleSortDemo [2; 3; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma454 : bubbleSortDemo [2; 3; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma455 : bubbleSortDemo [2; 3; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma456 : bubbleSortDemo [2; 3; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma457 : bubbleSortDemo [2; 3; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma458 : bubbleSortDemo [2; 3; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma459 : bubbleSortDemo [2; 3; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma460 : bubbleSortDemo [2; 3; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma461 : bubbleSortDemo [2; 3; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma462 : bubbleSortDemo [2; 4; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma463 : bubbleSortDemo [2; 4; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma464 : bubbleSortDemo [2; 4; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma465 : bubbleSortDemo [2; 4; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma466 : bubbleSortDemo [2; 4; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma467 : bubbleSortDemo [2; 4; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma468 : bubbleSortDemo [2; 4; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma469 : bubbleSortDemo [2; 4; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma470 : bubbleSortDemo [2; 4; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma471 : bubbleSortDemo [2; 4; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma472 : bubbleSortDemo [2; 4; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma473 : bubbleSortDemo [2; 4; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma474 : bubbleSortDemo [2; 4; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma475 : bubbleSortDemo [2; 4; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma476 : bubbleSortDemo [2; 4; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma477 : bubbleSortDemo [2; 4; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma478 : bubbleSortDemo [2; 4; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma479 : bubbleSortDemo [2; 4; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma480 : bubbleSortDemo [2; 4; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma481 : bubbleSortDemo [2; 4; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma482 : bubbleSortDemo [2; 4; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma483 : bubbleSortDemo [2; 4; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma484 : bubbleSortDemo [2; 4; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma485 : bubbleSortDemo [2; 4; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma486 : bubbleSortDemo [2; 5; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma487 : bubbleSortDemo [2; 5; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma488 : bubbleSortDemo [2; 5; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma489 : bubbleSortDemo [2; 5; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma490 : bubbleSortDemo [2; 5; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma491 : bubbleSortDemo [2; 5; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma492 : bubbleSortDemo [2; 5; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma493 : bubbleSortDemo [2; 5; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma494 : bubbleSortDemo [2; 5; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma495 : bubbleSortDemo [2; 5; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma496 : bubbleSortDemo [2; 5; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma497 : bubbleSortDemo [2; 5; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma498 : bubbleSortDemo [2; 5; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma499 : bubbleSortDemo [2; 5; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma500 : bubbleSortDemo [2; 5; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma501 : bubbleSortDemo [2; 5; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma502 : bubbleSortDemo [2; 5; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma503 : bubbleSortDemo [2; 5; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma504 : bubbleSortDemo [2; 5; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma505 : bubbleSortDemo [2; 5; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma506 : bubbleSortDemo [2; 5; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma507 : bubbleSortDemo [2; 5; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma508 : bubbleSortDemo [2; 5; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma509 : bubbleSortDemo [2; 5; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma510 : bubbleSortDemo [3; 0; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma511 : bubbleSortDemo [3; 0; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma512 : bubbleSortDemo [3; 0; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma513 : bubbleSortDemo [3; 0; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma514 : bubbleSortDemo [3; 0; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma515 : bubbleSortDemo [3; 0; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma516 : bubbleSortDemo [3; 0; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma517 : bubbleSortDemo [3; 0; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma518 : bubbleSortDemo [3; 0; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma519 : bubbleSortDemo [3; 0; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma520 : bubbleSortDemo [3; 0; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma521 : bubbleSortDemo [3; 0; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma522 : bubbleSortDemo [3; 0; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma523 : bubbleSortDemo [3; 0; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma524 : bubbleSortDemo [3; 0; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma525 : bubbleSortDemo [3; 0; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma526 : bubbleSortDemo [3; 0; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma527 : bubbleSortDemo [3; 0; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma528 : bubbleSortDemo [3; 0; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma529 : bubbleSortDemo [3; 0; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma530 : bubbleSortDemo [3; 0; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma531 : bubbleSortDemo [3; 0; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma532 : bubbleSortDemo [3; 0; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma533 : bubbleSortDemo [3; 0; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma534 : bubbleSortDemo [3; 1; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma535 : bubbleSortDemo [3; 1; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma536 : bubbleSortDemo [3; 1; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma537 : bubbleSortDemo [3; 1; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma538 : bubbleSortDemo [3; 1; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma539 : bubbleSortDemo [3; 1; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma540 : bubbleSortDemo [3; 1; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma541 : bubbleSortDemo [3; 1; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma542 : bubbleSortDemo [3; 1; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma543 : bubbleSortDemo [3; 1; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma544 : bubbleSortDemo [3; 1; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma545 : bubbleSortDemo [3; 1; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma546 : bubbleSortDemo [3; 1; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma547 : bubbleSortDemo [3; 1; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma548 : bubbleSortDemo [3; 1; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma549 : bubbleSortDemo [3; 1; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma550 : bubbleSortDemo [3; 1; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma551 : bubbleSortDemo [3; 1; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma552 : bubbleSortDemo [3; 1; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma553 : bubbleSortDemo [3; 1; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma554 : bubbleSortDemo [3; 1; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma555 : bubbleSortDemo [3; 1; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma556 : bubbleSortDemo [3; 1; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma557 : bubbleSortDemo [3; 1; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma558 : bubbleSortDemo [3; 2; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma559 : bubbleSortDemo [3; 2; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma560 : bubbleSortDemo [3; 2; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma561 : bubbleSortDemo [3; 2; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma562 : bubbleSortDemo [3; 2; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma563 : bubbleSortDemo [3; 2; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma564 : bubbleSortDemo [3; 2; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma565 : bubbleSortDemo [3; 2; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma566 : bubbleSortDemo [3; 2; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma567 : bubbleSortDemo [3; 2; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma568 : bubbleSortDemo [3; 2; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma569 : bubbleSortDemo [3; 2; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma570 : bubbleSortDemo [3; 2; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma571 : bubbleSortDemo [3; 2; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma572 : bubbleSortDemo [3; 2; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma573 : bubbleSortDemo [3; 2; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma574 : bubbleSortDemo [3; 2; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma575 : bubbleSortDemo [3; 2; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma576 : bubbleSortDemo [3; 2; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma577 : bubbleSortDemo [3; 2; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma578 : bubbleSortDemo [3; 2; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma579 : bubbleSortDemo [3; 2; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma580 : bubbleSortDemo [3; 2; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma581 : bubbleSortDemo [3; 2; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma582 : bubbleSortDemo [3; 4; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma583 : bubbleSortDemo [3; 4; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma584 : bubbleSortDemo [3; 4; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma585 : bubbleSortDemo [3; 4; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma586 : bubbleSortDemo [3; 4; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma587 : bubbleSortDemo [3; 4; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma588 : bubbleSortDemo [3; 4; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma589 : bubbleSortDemo [3; 4; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma590 : bubbleSortDemo [3; 4; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma591 : bubbleSortDemo [3; 4; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma592 : bubbleSortDemo [3; 4; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma593 : bubbleSortDemo [3; 4; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma594 : bubbleSortDemo [3; 4; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma595 : bubbleSortDemo [3; 4; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma596 : bubbleSortDemo [3; 4; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma597 : bubbleSortDemo [3; 4; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma598 : bubbleSortDemo [3; 4; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma599 : bubbleSortDemo [3; 4; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma600 : bubbleSortDemo [3; 4; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma601 : bubbleSortDemo [3; 4; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma602 : bubbleSortDemo [3; 4; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma603 : bubbleSortDemo [3; 4; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma604 : bubbleSortDemo [3; 4; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma605 : bubbleSortDemo [3; 4; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma606 : bubbleSortDemo [3; 5; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma607 : bubbleSortDemo [3; 5; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma608 : bubbleSortDemo [3; 5; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma609 : bubbleSortDemo [3; 5; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma610 : bubbleSortDemo [3; 5; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma611 : bubbleSortDemo [3; 5; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma612 : bubbleSortDemo [3; 5; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma613 : bubbleSortDemo [3; 5; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma614 : bubbleSortDemo [3; 5; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma615 : bubbleSortDemo [3; 5; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma616 : bubbleSortDemo [3; 5; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma617 : bubbleSortDemo [3; 5; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma618 : bubbleSortDemo [3; 5; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma619 : bubbleSortDemo [3; 5; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma620 : bubbleSortDemo [3; 5; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma621 : bubbleSortDemo [3; 5; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma622 : bubbleSortDemo [3; 5; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma623 : bubbleSortDemo [3; 5; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma624 : bubbleSortDemo [3; 5; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma625 : bubbleSortDemo [3; 5; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma626 : bubbleSortDemo [3; 5; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma627 : bubbleSortDemo [3; 5; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma628 : bubbleSortDemo [3; 5; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma629 : bubbleSortDemo [3; 5; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma630 : bubbleSortDemo [4; 0; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma631 : bubbleSortDemo [4; 0; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma632 : bubbleSortDemo [4; 0; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma633 : bubbleSortDemo [4; 0; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma634 : bubbleSortDemo [4; 0; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma635 : bubbleSortDemo [4; 0; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma636 : bubbleSortDemo [4; 0; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma637 : bubbleSortDemo [4; 0; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma638 : bubbleSortDemo [4; 0; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma639 : bubbleSortDemo [4; 0; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma640 : bubbleSortDemo [4; 0; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma641 : bubbleSortDemo [4; 0; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma642 : bubbleSortDemo [4; 0; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma643 : bubbleSortDemo [4; 0; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma644 : bubbleSortDemo [4; 0; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma645 : bubbleSortDemo [4; 0; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma646 : bubbleSortDemo [4; 0; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma647 : bubbleSortDemo [4; 0; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma648 : bubbleSortDemo [4; 0; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma649 : bubbleSortDemo [4; 0; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma650 : bubbleSortDemo [4; 0; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma651 : bubbleSortDemo [4; 0; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma652 : bubbleSortDemo [4; 0; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma653 : bubbleSortDemo [4; 0; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma654 : bubbleSortDemo [4; 1; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma655 : bubbleSortDemo [4; 1; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma656 : bubbleSortDemo [4; 1; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma657 : bubbleSortDemo [4; 1; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma658 : bubbleSortDemo [4; 1; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma659 : bubbleSortDemo [4; 1; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma660 : bubbleSortDemo [4; 1; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma661 : bubbleSortDemo [4; 1; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma662 : bubbleSortDemo [4; 1; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma663 : bubbleSortDemo [4; 1; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma664 : bubbleSortDemo [4; 1; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma665 : bubbleSortDemo [4; 1; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma666 : bubbleSortDemo [4; 1; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma667 : bubbleSortDemo [4; 1; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma668 : bubbleSortDemo [4; 1; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma669 : bubbleSortDemo [4; 1; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma670 : bubbleSortDemo [4; 1; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma671 : bubbleSortDemo [4; 1; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma672 : bubbleSortDemo [4; 1; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma673 : bubbleSortDemo [4; 1; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma674 : bubbleSortDemo [4; 1; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma675 : bubbleSortDemo [4; 1; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma676 : bubbleSortDemo [4; 1; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma677 : bubbleSortDemo [4; 1; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma678 : bubbleSortDemo [4; 2; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma679 : bubbleSortDemo [4; 2; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma680 : bubbleSortDemo [4; 2; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma681 : bubbleSortDemo [4; 2; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma682 : bubbleSortDemo [4; 2; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma683 : bubbleSortDemo [4; 2; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma684 : bubbleSortDemo [4; 2; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma685 : bubbleSortDemo [4; 2; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma686 : bubbleSortDemo [4; 2; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma687 : bubbleSortDemo [4; 2; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma688 : bubbleSortDemo [4; 2; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma689 : bubbleSortDemo [4; 2; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma690 : bubbleSortDemo [4; 2; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma691 : bubbleSortDemo [4; 2; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma692 : bubbleSortDemo [4; 2; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma693 : bubbleSortDemo [4; 2; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma694 : bubbleSortDemo [4; 2; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma695 : bubbleSortDemo [4; 2; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma696 : bubbleSortDemo [4; 2; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma697 : bubbleSortDemo [4; 2; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma698 : bubbleSortDemo [4; 2; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma699 : bubbleSortDemo [4; 2; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma700 : bubbleSortDemo [4; 2; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma701 : bubbleSortDemo [4; 2; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma702 : bubbleSortDemo [4; 3; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma703 : bubbleSortDemo [4; 3; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma704 : bubbleSortDemo [4; 3; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma705 : bubbleSortDemo [4; 3; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma706 : bubbleSortDemo [4; 3; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma707 : bubbleSortDemo [4; 3; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma708 : bubbleSortDemo [4; 3; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma709 : bubbleSortDemo [4; 3; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma710 : bubbleSortDemo [4; 3; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma711 : bubbleSortDemo [4; 3; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma712 : bubbleSortDemo [4; 3; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma713 : bubbleSortDemo [4; 3; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma714 : bubbleSortDemo [4; 3; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma715 : bubbleSortDemo [4; 3; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma716 : bubbleSortDemo [4; 3; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma717 : bubbleSortDemo [4; 3; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma718 : bubbleSortDemo [4; 3; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma719 : bubbleSortDemo [4; 3; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma720 : bubbleSortDemo [4; 3; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma721 : bubbleSortDemo [4; 3; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma722 : bubbleSortDemo [4; 3; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma723 : bubbleSortDemo [4; 3; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma724 : bubbleSortDemo [4; 3; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma725 : bubbleSortDemo [4; 3; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma726 : bubbleSortDemo [4; 5; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma727 : bubbleSortDemo [4; 5; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma728 : bubbleSortDemo [4; 5; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma729 : bubbleSortDemo [4; 5; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma730 : bubbleSortDemo [4; 5; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma731 : bubbleSortDemo [4; 5; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma732 : bubbleSortDemo [4; 5; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma733 : bubbleSortDemo [4; 5; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma734 : bubbleSortDemo [4; 5; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma735 : bubbleSortDemo [4; 5; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma736 : bubbleSortDemo [4; 5; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma737 : bubbleSortDemo [4; 5; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma738 : bubbleSortDemo [4; 5; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma739 : bubbleSortDemo [4; 5; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma740 : bubbleSortDemo [4; 5; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma741 : bubbleSortDemo [4; 5; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma742 : bubbleSortDemo [4; 5; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma743 : bubbleSortDemo [4; 5; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma744 : bubbleSortDemo [4; 5; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma745 : bubbleSortDemo [4; 5; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma746 : bubbleSortDemo [4; 5; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma747 : bubbleSortDemo [4; 5; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma748 : bubbleSortDemo [4; 5; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma749 : bubbleSortDemo [4; 5; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma750 : bubbleSortDemo [5; 0; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma751 : bubbleSortDemo [5; 0; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma752 : bubbleSortDemo [5; 0; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma753 : bubbleSortDemo [5; 0; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma754 : bubbleSortDemo [5; 0; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma755 : bubbleSortDemo [5; 0; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma756 : bubbleSortDemo [5; 0; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma757 : bubbleSortDemo [5; 0; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma758 : bubbleSortDemo [5; 0; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma759 : bubbleSortDemo [5; 0; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma760 : bubbleSortDemo [5; 0; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma761 : bubbleSortDemo [5; 0; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma762 : bubbleSortDemo [5; 0; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma763 : bubbleSortDemo [5; 0; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma764 : bubbleSortDemo [5; 0; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma765 : bubbleSortDemo [5; 0; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma766 : bubbleSortDemo [5; 0; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma767 : bubbleSortDemo [5; 0; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma768 : bubbleSortDemo [5; 0; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma769 : bubbleSortDemo [5; 0; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma770 : bubbleSortDemo [5; 0; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma771 : bubbleSortDemo [5; 0; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma772 : bubbleSortDemo [5; 0; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma773 : bubbleSortDemo [5; 0; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma774 : bubbleSortDemo [5; 1; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma775 : bubbleSortDemo [5; 1; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma776 : bubbleSortDemo [5; 1; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma777 : bubbleSortDemo [5; 1; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma778 : bubbleSortDemo [5; 1; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma779 : bubbleSortDemo [5; 1; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma780 : bubbleSortDemo [5; 1; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma781 : bubbleSortDemo [5; 1; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma782 : bubbleSortDemo [5; 1; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma783 : bubbleSortDemo [5; 1; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma784 : bubbleSortDemo [5; 1; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma785 : bubbleSortDemo [5; 1; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma786 : bubbleSortDemo [5; 1; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma787 : bubbleSortDemo [5; 1; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma788 : bubbleSortDemo [5; 1; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma789 : bubbleSortDemo [5; 1; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma790 : bubbleSortDemo [5; 1; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma791 : bubbleSortDemo [5; 1; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma792 : bubbleSortDemo [5; 1; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma793 : bubbleSortDemo [5; 1; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma794 : bubbleSortDemo [5; 1; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma795 : bubbleSortDemo [5; 1; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma796 : bubbleSortDemo [5; 1; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma797 : bubbleSortDemo [5; 1; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma798 : bubbleSortDemo [5; 2; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma799 : bubbleSortDemo [5; 2; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma800 : bubbleSortDemo [5; 2; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma801 : bubbleSortDemo [5; 2; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma802 : bubbleSortDemo [5; 2; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma803 : bubbleSortDemo [5; 2; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma804 : bubbleSortDemo [5; 2; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma805 : bubbleSortDemo [5; 2; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma806 : bubbleSortDemo [5; 2; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma807 : bubbleSortDemo [5; 2; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma808 : bubbleSortDemo [5; 2; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma809 : bubbleSortDemo [5; 2; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma810 : bubbleSortDemo [5; 2; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma811 : bubbleSortDemo [5; 2; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma812 : bubbleSortDemo [5; 2; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma813 : bubbleSortDemo [5; 2; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma814 : bubbleSortDemo [5; 2; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma815 : bubbleSortDemo [5; 2; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma816 : bubbleSortDemo [5; 2; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma817 : bubbleSortDemo [5; 2; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma818 : bubbleSortDemo [5; 2; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma819 : bubbleSortDemo [5; 2; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma820 : bubbleSortDemo [5; 2; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma821 : bubbleSortDemo [5; 2; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma822 : bubbleSortDemo [5; 3; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma823 : bubbleSortDemo [5; 3; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma824 : bubbleSortDemo [5; 3; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma825 : bubbleSortDemo [5; 3; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma826 : bubbleSortDemo [5; 3; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma827 : bubbleSortDemo [5; 3; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma828 : bubbleSortDemo [5; 3; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma829 : bubbleSortDemo [5; 3; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma830 : bubbleSortDemo [5; 3; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma831 : bubbleSortDemo [5; 3; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma832 : bubbleSortDemo [5; 3; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma833 : bubbleSortDemo [5; 3; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma834 : bubbleSortDemo [5; 3; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma835 : bubbleSortDemo [5; 3; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma836 : bubbleSortDemo [5; 3; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma837 : bubbleSortDemo [5; 3; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma838 : bubbleSortDemo [5; 3; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma839 : bubbleSortDemo [5; 3; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma840 : bubbleSortDemo [5; 3; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma841 : bubbleSortDemo [5; 3; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma842 : bubbleSortDemo [5; 3; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma843 : bubbleSortDemo [5; 3; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma844 : bubbleSortDemo [5; 3; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma845 : bubbleSortDemo [5; 3; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma846 : bubbleSortDemo [5; 4; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma847 : bubbleSortDemo [5; 4; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma848 : bubbleSortDemo [5; 4; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma849 : bubbleSortDemo [5; 4; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma850 : bubbleSortDemo [5; 4; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma851 : bubbleSortDemo [5; 4; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma852 : bubbleSortDemo [5; 4; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma853 : bubbleSortDemo [5; 4; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma854 : bubbleSortDemo [5; 4; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma855 : bubbleSortDemo [5; 4; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma856 : bubbleSortDemo [5; 4; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma857 : bubbleSortDemo [5; 4; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma858 : bubbleSortDemo [5; 4; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma859 : bubbleSortDemo [5; 4; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma860 : bubbleSortDemo [5; 4; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma861 : bubbleSortDemo [5; 4; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma862 : bubbleSortDemo [5; 4; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma863 : bubbleSortDemo [5; 4; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma864 : bubbleSortDemo [5; 4; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma865 : bubbleSortDemo [5; 4; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma866 : bubbleSortDemo [5; 4; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma867 : bubbleSortDemo [5; 4; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma868 : bubbleSortDemo [5; 4; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma bubbleSortTestLemma869 : bubbleSortDemo [5; 4; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.
