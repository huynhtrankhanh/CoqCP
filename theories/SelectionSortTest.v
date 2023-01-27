From stdpp Require Import numbers list.
From CoqCP Require Import SelectionSort.

Lemma selectionSortTestLemma0 : selectionSortDemo [0; 1; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma1 : selectionSortDemo [0; 2; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma2 : selectionSortDemo [1; 0; 2] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma3 : selectionSortDemo [1; 2; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma4 : selectionSortDemo [2; 0; 1] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma5 : selectionSortDemo [2; 1; 0] = [0; 1; 2].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma6 : selectionSortDemo [0; 1; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma7 : selectionSortDemo [0; 1; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma8 : selectionSortDemo [0; 2; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma9 : selectionSortDemo [0; 2; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma10 : selectionSortDemo [0; 3; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma11 : selectionSortDemo [0; 3; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma12 : selectionSortDemo [1; 0; 2; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma13 : selectionSortDemo [1; 0; 3; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma14 : selectionSortDemo [1; 2; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma15 : selectionSortDemo [1; 2; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma16 : selectionSortDemo [1; 3; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma17 : selectionSortDemo [1; 3; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma18 : selectionSortDemo [2; 0; 1; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma19 : selectionSortDemo [2; 0; 3; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma20 : selectionSortDemo [2; 1; 0; 3] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma21 : selectionSortDemo [2; 1; 3; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma22 : selectionSortDemo [2; 3; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma23 : selectionSortDemo [2; 3; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma24 : selectionSortDemo [3; 0; 1; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma25 : selectionSortDemo [3; 0; 2; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma26 : selectionSortDemo [3; 1; 0; 2] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma27 : selectionSortDemo [3; 1; 2; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma28 : selectionSortDemo [3; 2; 0; 1] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma29 : selectionSortDemo [3; 2; 1; 0] = [0; 1; 2; 3].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma30 : selectionSortDemo [0; 1; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma31 : selectionSortDemo [0; 1; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma32 : selectionSortDemo [0; 1; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma33 : selectionSortDemo [0; 1; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma34 : selectionSortDemo [0; 1; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma35 : selectionSortDemo [0; 1; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma36 : selectionSortDemo [0; 2; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma37 : selectionSortDemo [0; 2; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma38 : selectionSortDemo [0; 2; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma39 : selectionSortDemo [0; 2; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma40 : selectionSortDemo [0; 2; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma41 : selectionSortDemo [0; 2; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma42 : selectionSortDemo [0; 3; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma43 : selectionSortDemo [0; 3; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma44 : selectionSortDemo [0; 3; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma45 : selectionSortDemo [0; 3; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma46 : selectionSortDemo [0; 3; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma47 : selectionSortDemo [0; 3; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma48 : selectionSortDemo [0; 4; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma49 : selectionSortDemo [0; 4; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma50 : selectionSortDemo [0; 4; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma51 : selectionSortDemo [0; 4; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma52 : selectionSortDemo [0; 4; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma53 : selectionSortDemo [0; 4; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma54 : selectionSortDemo [1; 0; 2; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma55 : selectionSortDemo [1; 0; 2; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma56 : selectionSortDemo [1; 0; 3; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma57 : selectionSortDemo [1; 0; 3; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma58 : selectionSortDemo [1; 0; 4; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma59 : selectionSortDemo [1; 0; 4; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma60 : selectionSortDemo [1; 2; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma61 : selectionSortDemo [1; 2; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma62 : selectionSortDemo [1; 2; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma63 : selectionSortDemo [1; 2; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma64 : selectionSortDemo [1; 2; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma65 : selectionSortDemo [1; 2; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma66 : selectionSortDemo [1; 3; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma67 : selectionSortDemo [1; 3; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma68 : selectionSortDemo [1; 3; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma69 : selectionSortDemo [1; 3; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma70 : selectionSortDemo [1; 3; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma71 : selectionSortDemo [1; 3; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma72 : selectionSortDemo [1; 4; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma73 : selectionSortDemo [1; 4; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma74 : selectionSortDemo [1; 4; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma75 : selectionSortDemo [1; 4; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma76 : selectionSortDemo [1; 4; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma77 : selectionSortDemo [1; 4; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma78 : selectionSortDemo [2; 0; 1; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma79 : selectionSortDemo [2; 0; 1; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma80 : selectionSortDemo [2; 0; 3; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma81 : selectionSortDemo [2; 0; 3; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma82 : selectionSortDemo [2; 0; 4; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma83 : selectionSortDemo [2; 0; 4; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma84 : selectionSortDemo [2; 1; 0; 3; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma85 : selectionSortDemo [2; 1; 0; 4; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma86 : selectionSortDemo [2; 1; 3; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma87 : selectionSortDemo [2; 1; 3; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma88 : selectionSortDemo [2; 1; 4; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma89 : selectionSortDemo [2; 1; 4; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma90 : selectionSortDemo [2; 3; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma91 : selectionSortDemo [2; 3; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma92 : selectionSortDemo [2; 3; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma93 : selectionSortDemo [2; 3; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma94 : selectionSortDemo [2; 3; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma95 : selectionSortDemo [2; 3; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma96 : selectionSortDemo [2; 4; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma97 : selectionSortDemo [2; 4; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma98 : selectionSortDemo [2; 4; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma99 : selectionSortDemo [2; 4; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma100 : selectionSortDemo [2; 4; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma101 : selectionSortDemo [2; 4; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma102 : selectionSortDemo [3; 0; 1; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma103 : selectionSortDemo [3; 0; 1; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma104 : selectionSortDemo [3; 0; 2; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma105 : selectionSortDemo [3; 0; 2; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma106 : selectionSortDemo [3; 0; 4; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma107 : selectionSortDemo [3; 0; 4; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma108 : selectionSortDemo [3; 1; 0; 2; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma109 : selectionSortDemo [3; 1; 0; 4; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma110 : selectionSortDemo [3; 1; 2; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma111 : selectionSortDemo [3; 1; 2; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma112 : selectionSortDemo [3; 1; 4; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma113 : selectionSortDemo [3; 1; 4; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma114 : selectionSortDemo [3; 2; 0; 1; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma115 : selectionSortDemo [3; 2; 0; 4; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma116 : selectionSortDemo [3; 2; 1; 0; 4] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma117 : selectionSortDemo [3; 2; 1; 4; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma118 : selectionSortDemo [3; 2; 4; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma119 : selectionSortDemo [3; 2; 4; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma120 : selectionSortDemo [3; 4; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma121 : selectionSortDemo [3; 4; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma122 : selectionSortDemo [3; 4; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma123 : selectionSortDemo [3; 4; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma124 : selectionSortDemo [3; 4; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma125 : selectionSortDemo [3; 4; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma126 : selectionSortDemo [4; 0; 1; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma127 : selectionSortDemo [4; 0; 1; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma128 : selectionSortDemo [4; 0; 2; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma129 : selectionSortDemo [4; 0; 2; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma130 : selectionSortDemo [4; 0; 3; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma131 : selectionSortDemo [4; 0; 3; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma132 : selectionSortDemo [4; 1; 0; 2; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma133 : selectionSortDemo [4; 1; 0; 3; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma134 : selectionSortDemo [4; 1; 2; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma135 : selectionSortDemo [4; 1; 2; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma136 : selectionSortDemo [4; 1; 3; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma137 : selectionSortDemo [4; 1; 3; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma138 : selectionSortDemo [4; 2; 0; 1; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma139 : selectionSortDemo [4; 2; 0; 3; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma140 : selectionSortDemo [4; 2; 1; 0; 3] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma141 : selectionSortDemo [4; 2; 1; 3; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma142 : selectionSortDemo [4; 2; 3; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma143 : selectionSortDemo [4; 2; 3; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma144 : selectionSortDemo [4; 3; 0; 1; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma145 : selectionSortDemo [4; 3; 0; 2; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma146 : selectionSortDemo [4; 3; 1; 0; 2] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma147 : selectionSortDemo [4; 3; 1; 2; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma148 : selectionSortDemo [4; 3; 2; 0; 1] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma149 : selectionSortDemo [4; 3; 2; 1; 0] = [0; 1; 2; 3; 4].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma150 : selectionSortDemo [0; 1; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma151 : selectionSortDemo [0; 1; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma152 : selectionSortDemo [0; 1; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma153 : selectionSortDemo [0; 1; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma154 : selectionSortDemo [0; 1; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma155 : selectionSortDemo [0; 1; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma156 : selectionSortDemo [0; 1; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma157 : selectionSortDemo [0; 1; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma158 : selectionSortDemo [0; 1; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma159 : selectionSortDemo [0; 1; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma160 : selectionSortDemo [0; 1; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma161 : selectionSortDemo [0; 1; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma162 : selectionSortDemo [0; 1; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma163 : selectionSortDemo [0; 1; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma164 : selectionSortDemo [0; 1; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma165 : selectionSortDemo [0; 1; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma166 : selectionSortDemo [0; 1; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma167 : selectionSortDemo [0; 1; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma168 : selectionSortDemo [0; 1; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma169 : selectionSortDemo [0; 1; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma170 : selectionSortDemo [0; 1; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma171 : selectionSortDemo [0; 1; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma172 : selectionSortDemo [0; 1; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma173 : selectionSortDemo [0; 1; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma174 : selectionSortDemo [0; 2; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma175 : selectionSortDemo [0; 2; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma176 : selectionSortDemo [0; 2; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma177 : selectionSortDemo [0; 2; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma178 : selectionSortDemo [0; 2; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma179 : selectionSortDemo [0; 2; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma180 : selectionSortDemo [0; 2; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma181 : selectionSortDemo [0; 2; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma182 : selectionSortDemo [0; 2; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma183 : selectionSortDemo [0; 2; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma184 : selectionSortDemo [0; 2; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma185 : selectionSortDemo [0; 2; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma186 : selectionSortDemo [0; 2; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma187 : selectionSortDemo [0; 2; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma188 : selectionSortDemo [0; 2; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma189 : selectionSortDemo [0; 2; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma190 : selectionSortDemo [0; 2; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma191 : selectionSortDemo [0; 2; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma192 : selectionSortDemo [0; 2; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma193 : selectionSortDemo [0; 2; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma194 : selectionSortDemo [0; 2; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma195 : selectionSortDemo [0; 2; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma196 : selectionSortDemo [0; 2; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma197 : selectionSortDemo [0; 2; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma198 : selectionSortDemo [0; 3; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma199 : selectionSortDemo [0; 3; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma200 : selectionSortDemo [0; 3; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma201 : selectionSortDemo [0; 3; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma202 : selectionSortDemo [0; 3; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma203 : selectionSortDemo [0; 3; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma204 : selectionSortDemo [0; 3; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma205 : selectionSortDemo [0; 3; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma206 : selectionSortDemo [0; 3; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma207 : selectionSortDemo [0; 3; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma208 : selectionSortDemo [0; 3; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma209 : selectionSortDemo [0; 3; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma210 : selectionSortDemo [0; 3; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma211 : selectionSortDemo [0; 3; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma212 : selectionSortDemo [0; 3; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma213 : selectionSortDemo [0; 3; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma214 : selectionSortDemo [0; 3; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma215 : selectionSortDemo [0; 3; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma216 : selectionSortDemo [0; 3; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma217 : selectionSortDemo [0; 3; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma218 : selectionSortDemo [0; 3; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma219 : selectionSortDemo [0; 3; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma220 : selectionSortDemo [0; 3; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma221 : selectionSortDemo [0; 3; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma222 : selectionSortDemo [0; 4; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma223 : selectionSortDemo [0; 4; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma224 : selectionSortDemo [0; 4; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma225 : selectionSortDemo [0; 4; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma226 : selectionSortDemo [0; 4; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma227 : selectionSortDemo [0; 4; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma228 : selectionSortDemo [0; 4; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma229 : selectionSortDemo [0; 4; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma230 : selectionSortDemo [0; 4; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma231 : selectionSortDemo [0; 4; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma232 : selectionSortDemo [0; 4; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma233 : selectionSortDemo [0; 4; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma234 : selectionSortDemo [0; 4; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma235 : selectionSortDemo [0; 4; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma236 : selectionSortDemo [0; 4; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma237 : selectionSortDemo [0; 4; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma238 : selectionSortDemo [0; 4; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma239 : selectionSortDemo [0; 4; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma240 : selectionSortDemo [0; 4; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma241 : selectionSortDemo [0; 4; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma242 : selectionSortDemo [0; 4; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma243 : selectionSortDemo [0; 4; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma244 : selectionSortDemo [0; 4; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma245 : selectionSortDemo [0; 4; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma246 : selectionSortDemo [0; 5; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma247 : selectionSortDemo [0; 5; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma248 : selectionSortDemo [0; 5; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma249 : selectionSortDemo [0; 5; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma250 : selectionSortDemo [0; 5; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma251 : selectionSortDemo [0; 5; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma252 : selectionSortDemo [0; 5; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma253 : selectionSortDemo [0; 5; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma254 : selectionSortDemo [0; 5; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma255 : selectionSortDemo [0; 5; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma256 : selectionSortDemo [0; 5; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma257 : selectionSortDemo [0; 5; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma258 : selectionSortDemo [0; 5; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma259 : selectionSortDemo [0; 5; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma260 : selectionSortDemo [0; 5; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma261 : selectionSortDemo [0; 5; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma262 : selectionSortDemo [0; 5; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma263 : selectionSortDemo [0; 5; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma264 : selectionSortDemo [0; 5; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma265 : selectionSortDemo [0; 5; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma266 : selectionSortDemo [0; 5; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma267 : selectionSortDemo [0; 5; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma268 : selectionSortDemo [0; 5; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma269 : selectionSortDemo [0; 5; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma270 : selectionSortDemo [1; 0; 2; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma271 : selectionSortDemo [1; 0; 2; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma272 : selectionSortDemo [1; 0; 2; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma273 : selectionSortDemo [1; 0; 2; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma274 : selectionSortDemo [1; 0; 2; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma275 : selectionSortDemo [1; 0; 2; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma276 : selectionSortDemo [1; 0; 3; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma277 : selectionSortDemo [1; 0; 3; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma278 : selectionSortDemo [1; 0; 3; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma279 : selectionSortDemo [1; 0; 3; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma280 : selectionSortDemo [1; 0; 3; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma281 : selectionSortDemo [1; 0; 3; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma282 : selectionSortDemo [1; 0; 4; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma283 : selectionSortDemo [1; 0; 4; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma284 : selectionSortDemo [1; 0; 4; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma285 : selectionSortDemo [1; 0; 4; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma286 : selectionSortDemo [1; 0; 4; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma287 : selectionSortDemo [1; 0; 4; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma288 : selectionSortDemo [1; 0; 5; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma289 : selectionSortDemo [1; 0; 5; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma290 : selectionSortDemo [1; 0; 5; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma291 : selectionSortDemo [1; 0; 5; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma292 : selectionSortDemo [1; 0; 5; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma293 : selectionSortDemo [1; 0; 5; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma294 : selectionSortDemo [1; 2; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma295 : selectionSortDemo [1; 2; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma296 : selectionSortDemo [1; 2; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma297 : selectionSortDemo [1; 2; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma298 : selectionSortDemo [1; 2; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma299 : selectionSortDemo [1; 2; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma300 : selectionSortDemo [1; 2; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma301 : selectionSortDemo [1; 2; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma302 : selectionSortDemo [1; 2; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma303 : selectionSortDemo [1; 2; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma304 : selectionSortDemo [1; 2; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma305 : selectionSortDemo [1; 2; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma306 : selectionSortDemo [1; 2; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma307 : selectionSortDemo [1; 2; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma308 : selectionSortDemo [1; 2; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma309 : selectionSortDemo [1; 2; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma310 : selectionSortDemo [1; 2; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma311 : selectionSortDemo [1; 2; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma312 : selectionSortDemo [1; 2; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma313 : selectionSortDemo [1; 2; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma314 : selectionSortDemo [1; 2; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma315 : selectionSortDemo [1; 2; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma316 : selectionSortDemo [1; 2; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma317 : selectionSortDemo [1; 2; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma318 : selectionSortDemo [1; 3; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma319 : selectionSortDemo [1; 3; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma320 : selectionSortDemo [1; 3; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma321 : selectionSortDemo [1; 3; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma322 : selectionSortDemo [1; 3; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma323 : selectionSortDemo [1; 3; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma324 : selectionSortDemo [1; 3; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma325 : selectionSortDemo [1; 3; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma326 : selectionSortDemo [1; 3; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma327 : selectionSortDemo [1; 3; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma328 : selectionSortDemo [1; 3; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma329 : selectionSortDemo [1; 3; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma330 : selectionSortDemo [1; 3; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma331 : selectionSortDemo [1; 3; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma332 : selectionSortDemo [1; 3; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma333 : selectionSortDemo [1; 3; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma334 : selectionSortDemo [1; 3; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma335 : selectionSortDemo [1; 3; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma336 : selectionSortDemo [1; 3; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma337 : selectionSortDemo [1; 3; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma338 : selectionSortDemo [1; 3; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma339 : selectionSortDemo [1; 3; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma340 : selectionSortDemo [1; 3; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma341 : selectionSortDemo [1; 3; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma342 : selectionSortDemo [1; 4; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma343 : selectionSortDemo [1; 4; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma344 : selectionSortDemo [1; 4; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma345 : selectionSortDemo [1; 4; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma346 : selectionSortDemo [1; 4; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma347 : selectionSortDemo [1; 4; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma348 : selectionSortDemo [1; 4; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma349 : selectionSortDemo [1; 4; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma350 : selectionSortDemo [1; 4; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma351 : selectionSortDemo [1; 4; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma352 : selectionSortDemo [1; 4; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma353 : selectionSortDemo [1; 4; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma354 : selectionSortDemo [1; 4; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma355 : selectionSortDemo [1; 4; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma356 : selectionSortDemo [1; 4; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma357 : selectionSortDemo [1; 4; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma358 : selectionSortDemo [1; 4; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma359 : selectionSortDemo [1; 4; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma360 : selectionSortDemo [1; 4; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma361 : selectionSortDemo [1; 4; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma362 : selectionSortDemo [1; 4; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma363 : selectionSortDemo [1; 4; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma364 : selectionSortDemo [1; 4; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma365 : selectionSortDemo [1; 4; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma366 : selectionSortDemo [1; 5; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma367 : selectionSortDemo [1; 5; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma368 : selectionSortDemo [1; 5; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma369 : selectionSortDemo [1; 5; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma370 : selectionSortDemo [1; 5; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma371 : selectionSortDemo [1; 5; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma372 : selectionSortDemo [1; 5; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma373 : selectionSortDemo [1; 5; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma374 : selectionSortDemo [1; 5; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma375 : selectionSortDemo [1; 5; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma376 : selectionSortDemo [1; 5; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma377 : selectionSortDemo [1; 5; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma378 : selectionSortDemo [1; 5; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma379 : selectionSortDemo [1; 5; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma380 : selectionSortDemo [1; 5; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma381 : selectionSortDemo [1; 5; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma382 : selectionSortDemo [1; 5; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma383 : selectionSortDemo [1; 5; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma384 : selectionSortDemo [1; 5; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma385 : selectionSortDemo [1; 5; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma386 : selectionSortDemo [1; 5; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma387 : selectionSortDemo [1; 5; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma388 : selectionSortDemo [1; 5; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma389 : selectionSortDemo [1; 5; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma390 : selectionSortDemo [2; 0; 1; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma391 : selectionSortDemo [2; 0; 1; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma392 : selectionSortDemo [2; 0; 1; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma393 : selectionSortDemo [2; 0; 1; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma394 : selectionSortDemo [2; 0; 1; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma395 : selectionSortDemo [2; 0; 1; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma396 : selectionSortDemo [2; 0; 3; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma397 : selectionSortDemo [2; 0; 3; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma398 : selectionSortDemo [2; 0; 3; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma399 : selectionSortDemo [2; 0; 3; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma400 : selectionSortDemo [2; 0; 3; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma401 : selectionSortDemo [2; 0; 3; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma402 : selectionSortDemo [2; 0; 4; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma403 : selectionSortDemo [2; 0; 4; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma404 : selectionSortDemo [2; 0; 4; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma405 : selectionSortDemo [2; 0; 4; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma406 : selectionSortDemo [2; 0; 4; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma407 : selectionSortDemo [2; 0; 4; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma408 : selectionSortDemo [2; 0; 5; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma409 : selectionSortDemo [2; 0; 5; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma410 : selectionSortDemo [2; 0; 5; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma411 : selectionSortDemo [2; 0; 5; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma412 : selectionSortDemo [2; 0; 5; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma413 : selectionSortDemo [2; 0; 5; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma414 : selectionSortDemo [2; 1; 0; 3; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma415 : selectionSortDemo [2; 1; 0; 3; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma416 : selectionSortDemo [2; 1; 0; 4; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma417 : selectionSortDemo [2; 1; 0; 4; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma418 : selectionSortDemo [2; 1; 0; 5; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma419 : selectionSortDemo [2; 1; 0; 5; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma420 : selectionSortDemo [2; 1; 3; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma421 : selectionSortDemo [2; 1; 3; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma422 : selectionSortDemo [2; 1; 3; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma423 : selectionSortDemo [2; 1; 3; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma424 : selectionSortDemo [2; 1; 3; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma425 : selectionSortDemo [2; 1; 3; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma426 : selectionSortDemo [2; 1; 4; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma427 : selectionSortDemo [2; 1; 4; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma428 : selectionSortDemo [2; 1; 4; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma429 : selectionSortDemo [2; 1; 4; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma430 : selectionSortDemo [2; 1; 4; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma431 : selectionSortDemo [2; 1; 4; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma432 : selectionSortDemo [2; 1; 5; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma433 : selectionSortDemo [2; 1; 5; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma434 : selectionSortDemo [2; 1; 5; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma435 : selectionSortDemo [2; 1; 5; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma436 : selectionSortDemo [2; 1; 5; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma437 : selectionSortDemo [2; 1; 5; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma438 : selectionSortDemo [2; 3; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma439 : selectionSortDemo [2; 3; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma440 : selectionSortDemo [2; 3; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma441 : selectionSortDemo [2; 3; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma442 : selectionSortDemo [2; 3; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma443 : selectionSortDemo [2; 3; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma444 : selectionSortDemo [2; 3; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma445 : selectionSortDemo [2; 3; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma446 : selectionSortDemo [2; 3; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma447 : selectionSortDemo [2; 3; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma448 : selectionSortDemo [2; 3; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma449 : selectionSortDemo [2; 3; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma450 : selectionSortDemo [2; 3; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma451 : selectionSortDemo [2; 3; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma452 : selectionSortDemo [2; 3; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma453 : selectionSortDemo [2; 3; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma454 : selectionSortDemo [2; 3; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma455 : selectionSortDemo [2; 3; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma456 : selectionSortDemo [2; 3; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma457 : selectionSortDemo [2; 3; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma458 : selectionSortDemo [2; 3; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma459 : selectionSortDemo [2; 3; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma460 : selectionSortDemo [2; 3; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma461 : selectionSortDemo [2; 3; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma462 : selectionSortDemo [2; 4; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma463 : selectionSortDemo [2; 4; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma464 : selectionSortDemo [2; 4; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma465 : selectionSortDemo [2; 4; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma466 : selectionSortDemo [2; 4; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma467 : selectionSortDemo [2; 4; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma468 : selectionSortDemo [2; 4; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma469 : selectionSortDemo [2; 4; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma470 : selectionSortDemo [2; 4; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma471 : selectionSortDemo [2; 4; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma472 : selectionSortDemo [2; 4; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma473 : selectionSortDemo [2; 4; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma474 : selectionSortDemo [2; 4; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma475 : selectionSortDemo [2; 4; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma476 : selectionSortDemo [2; 4; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma477 : selectionSortDemo [2; 4; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma478 : selectionSortDemo [2; 4; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma479 : selectionSortDemo [2; 4; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma480 : selectionSortDemo [2; 4; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma481 : selectionSortDemo [2; 4; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma482 : selectionSortDemo [2; 4; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma483 : selectionSortDemo [2; 4; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma484 : selectionSortDemo [2; 4; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma485 : selectionSortDemo [2; 4; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma486 : selectionSortDemo [2; 5; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma487 : selectionSortDemo [2; 5; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma488 : selectionSortDemo [2; 5; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma489 : selectionSortDemo [2; 5; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma490 : selectionSortDemo [2; 5; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma491 : selectionSortDemo [2; 5; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma492 : selectionSortDemo [2; 5; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma493 : selectionSortDemo [2; 5; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma494 : selectionSortDemo [2; 5; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma495 : selectionSortDemo [2; 5; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma496 : selectionSortDemo [2; 5; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma497 : selectionSortDemo [2; 5; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma498 : selectionSortDemo [2; 5; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma499 : selectionSortDemo [2; 5; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma500 : selectionSortDemo [2; 5; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma501 : selectionSortDemo [2; 5; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma502 : selectionSortDemo [2; 5; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma503 : selectionSortDemo [2; 5; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma504 : selectionSortDemo [2; 5; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma505 : selectionSortDemo [2; 5; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma506 : selectionSortDemo [2; 5; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma507 : selectionSortDemo [2; 5; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma508 : selectionSortDemo [2; 5; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma509 : selectionSortDemo [2; 5; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma510 : selectionSortDemo [3; 0; 1; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma511 : selectionSortDemo [3; 0; 1; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma512 : selectionSortDemo [3; 0; 1; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma513 : selectionSortDemo [3; 0; 1; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma514 : selectionSortDemo [3; 0; 1; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma515 : selectionSortDemo [3; 0; 1; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma516 : selectionSortDemo [3; 0; 2; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma517 : selectionSortDemo [3; 0; 2; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma518 : selectionSortDemo [3; 0; 2; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma519 : selectionSortDemo [3; 0; 2; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma520 : selectionSortDemo [3; 0; 2; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma521 : selectionSortDemo [3; 0; 2; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma522 : selectionSortDemo [3; 0; 4; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma523 : selectionSortDemo [3; 0; 4; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma524 : selectionSortDemo [3; 0; 4; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma525 : selectionSortDemo [3; 0; 4; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma526 : selectionSortDemo [3; 0; 4; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma527 : selectionSortDemo [3; 0; 4; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma528 : selectionSortDemo [3; 0; 5; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma529 : selectionSortDemo [3; 0; 5; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma530 : selectionSortDemo [3; 0; 5; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma531 : selectionSortDemo [3; 0; 5; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma532 : selectionSortDemo [3; 0; 5; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma533 : selectionSortDemo [3; 0; 5; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma534 : selectionSortDemo [3; 1; 0; 2; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma535 : selectionSortDemo [3; 1; 0; 2; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma536 : selectionSortDemo [3; 1; 0; 4; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma537 : selectionSortDemo [3; 1; 0; 4; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma538 : selectionSortDemo [3; 1; 0; 5; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma539 : selectionSortDemo [3; 1; 0; 5; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma540 : selectionSortDemo [3; 1; 2; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma541 : selectionSortDemo [3; 1; 2; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma542 : selectionSortDemo [3; 1; 2; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma543 : selectionSortDemo [3; 1; 2; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma544 : selectionSortDemo [3; 1; 2; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma545 : selectionSortDemo [3; 1; 2; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma546 : selectionSortDemo [3; 1; 4; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma547 : selectionSortDemo [3; 1; 4; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma548 : selectionSortDemo [3; 1; 4; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma549 : selectionSortDemo [3; 1; 4; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma550 : selectionSortDemo [3; 1; 4; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma551 : selectionSortDemo [3; 1; 4; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma552 : selectionSortDemo [3; 1; 5; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma553 : selectionSortDemo [3; 1; 5; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma554 : selectionSortDemo [3; 1; 5; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma555 : selectionSortDemo [3; 1; 5; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma556 : selectionSortDemo [3; 1; 5; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma557 : selectionSortDemo [3; 1; 5; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma558 : selectionSortDemo [3; 2; 0; 1; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma559 : selectionSortDemo [3; 2; 0; 1; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma560 : selectionSortDemo [3; 2; 0; 4; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma561 : selectionSortDemo [3; 2; 0; 4; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma562 : selectionSortDemo [3; 2; 0; 5; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma563 : selectionSortDemo [3; 2; 0; 5; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma564 : selectionSortDemo [3; 2; 1; 0; 4; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma565 : selectionSortDemo [3; 2; 1; 0; 5; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma566 : selectionSortDemo [3; 2; 1; 4; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma567 : selectionSortDemo [3; 2; 1; 4; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma568 : selectionSortDemo [3; 2; 1; 5; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma569 : selectionSortDemo [3; 2; 1; 5; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma570 : selectionSortDemo [3; 2; 4; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma571 : selectionSortDemo [3; 2; 4; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma572 : selectionSortDemo [3; 2; 4; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma573 : selectionSortDemo [3; 2; 4; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma574 : selectionSortDemo [3; 2; 4; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma575 : selectionSortDemo [3; 2; 4; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma576 : selectionSortDemo [3; 2; 5; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma577 : selectionSortDemo [3; 2; 5; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma578 : selectionSortDemo [3; 2; 5; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma579 : selectionSortDemo [3; 2; 5; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma580 : selectionSortDemo [3; 2; 5; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma581 : selectionSortDemo [3; 2; 5; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma582 : selectionSortDemo [3; 4; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma583 : selectionSortDemo [3; 4; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma584 : selectionSortDemo [3; 4; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma585 : selectionSortDemo [3; 4; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma586 : selectionSortDemo [3; 4; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma587 : selectionSortDemo [3; 4; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma588 : selectionSortDemo [3; 4; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma589 : selectionSortDemo [3; 4; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma590 : selectionSortDemo [3; 4; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma591 : selectionSortDemo [3; 4; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma592 : selectionSortDemo [3; 4; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma593 : selectionSortDemo [3; 4; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma594 : selectionSortDemo [3; 4; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma595 : selectionSortDemo [3; 4; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma596 : selectionSortDemo [3; 4; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma597 : selectionSortDemo [3; 4; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma598 : selectionSortDemo [3; 4; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma599 : selectionSortDemo [3; 4; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma600 : selectionSortDemo [3; 4; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma601 : selectionSortDemo [3; 4; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma602 : selectionSortDemo [3; 4; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma603 : selectionSortDemo [3; 4; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma604 : selectionSortDemo [3; 4; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma605 : selectionSortDemo [3; 4; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma606 : selectionSortDemo [3; 5; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma607 : selectionSortDemo [3; 5; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma608 : selectionSortDemo [3; 5; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma609 : selectionSortDemo [3; 5; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma610 : selectionSortDemo [3; 5; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma611 : selectionSortDemo [3; 5; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma612 : selectionSortDemo [3; 5; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma613 : selectionSortDemo [3; 5; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma614 : selectionSortDemo [3; 5; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma615 : selectionSortDemo [3; 5; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma616 : selectionSortDemo [3; 5; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma617 : selectionSortDemo [3; 5; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma618 : selectionSortDemo [3; 5; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma619 : selectionSortDemo [3; 5; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma620 : selectionSortDemo [3; 5; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma621 : selectionSortDemo [3; 5; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma622 : selectionSortDemo [3; 5; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma623 : selectionSortDemo [3; 5; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma624 : selectionSortDemo [3; 5; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma625 : selectionSortDemo [3; 5; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma626 : selectionSortDemo [3; 5; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma627 : selectionSortDemo [3; 5; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma628 : selectionSortDemo [3; 5; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma629 : selectionSortDemo [3; 5; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma630 : selectionSortDemo [4; 0; 1; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma631 : selectionSortDemo [4; 0; 1; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma632 : selectionSortDemo [4; 0; 1; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma633 : selectionSortDemo [4; 0; 1; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma634 : selectionSortDemo [4; 0; 1; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma635 : selectionSortDemo [4; 0; 1; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma636 : selectionSortDemo [4; 0; 2; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma637 : selectionSortDemo [4; 0; 2; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma638 : selectionSortDemo [4; 0; 2; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma639 : selectionSortDemo [4; 0; 2; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma640 : selectionSortDemo [4; 0; 2; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma641 : selectionSortDemo [4; 0; 2; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma642 : selectionSortDemo [4; 0; 3; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma643 : selectionSortDemo [4; 0; 3; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma644 : selectionSortDemo [4; 0; 3; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma645 : selectionSortDemo [4; 0; 3; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma646 : selectionSortDemo [4; 0; 3; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma647 : selectionSortDemo [4; 0; 3; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma648 : selectionSortDemo [4; 0; 5; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma649 : selectionSortDemo [4; 0; 5; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma650 : selectionSortDemo [4; 0; 5; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma651 : selectionSortDemo [4; 0; 5; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma652 : selectionSortDemo [4; 0; 5; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma653 : selectionSortDemo [4; 0; 5; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma654 : selectionSortDemo [4; 1; 0; 2; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma655 : selectionSortDemo [4; 1; 0; 2; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma656 : selectionSortDemo [4; 1; 0; 3; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma657 : selectionSortDemo [4; 1; 0; 3; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma658 : selectionSortDemo [4; 1; 0; 5; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma659 : selectionSortDemo [4; 1; 0; 5; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma660 : selectionSortDemo [4; 1; 2; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma661 : selectionSortDemo [4; 1; 2; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma662 : selectionSortDemo [4; 1; 2; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma663 : selectionSortDemo [4; 1; 2; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma664 : selectionSortDemo [4; 1; 2; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma665 : selectionSortDemo [4; 1; 2; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma666 : selectionSortDemo [4; 1; 3; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma667 : selectionSortDemo [4; 1; 3; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma668 : selectionSortDemo [4; 1; 3; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma669 : selectionSortDemo [4; 1; 3; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma670 : selectionSortDemo [4; 1; 3; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma671 : selectionSortDemo [4; 1; 3; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma672 : selectionSortDemo [4; 1; 5; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma673 : selectionSortDemo [4; 1; 5; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma674 : selectionSortDemo [4; 1; 5; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma675 : selectionSortDemo [4; 1; 5; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma676 : selectionSortDemo [4; 1; 5; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma677 : selectionSortDemo [4; 1; 5; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma678 : selectionSortDemo [4; 2; 0; 1; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma679 : selectionSortDemo [4; 2; 0; 1; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma680 : selectionSortDemo [4; 2; 0; 3; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma681 : selectionSortDemo [4; 2; 0; 3; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma682 : selectionSortDemo [4; 2; 0; 5; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma683 : selectionSortDemo [4; 2; 0; 5; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma684 : selectionSortDemo [4; 2; 1; 0; 3; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma685 : selectionSortDemo [4; 2; 1; 0; 5; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma686 : selectionSortDemo [4; 2; 1; 3; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma687 : selectionSortDemo [4; 2; 1; 3; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma688 : selectionSortDemo [4; 2; 1; 5; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma689 : selectionSortDemo [4; 2; 1; 5; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma690 : selectionSortDemo [4; 2; 3; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma691 : selectionSortDemo [4; 2; 3; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma692 : selectionSortDemo [4; 2; 3; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma693 : selectionSortDemo [4; 2; 3; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma694 : selectionSortDemo [4; 2; 3; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma695 : selectionSortDemo [4; 2; 3; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma696 : selectionSortDemo [4; 2; 5; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma697 : selectionSortDemo [4; 2; 5; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma698 : selectionSortDemo [4; 2; 5; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma699 : selectionSortDemo [4; 2; 5; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma700 : selectionSortDemo [4; 2; 5; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma701 : selectionSortDemo [4; 2; 5; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma702 : selectionSortDemo [4; 3; 0; 1; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma703 : selectionSortDemo [4; 3; 0; 1; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma704 : selectionSortDemo [4; 3; 0; 2; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma705 : selectionSortDemo [4; 3; 0; 2; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma706 : selectionSortDemo [4; 3; 0; 5; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma707 : selectionSortDemo [4; 3; 0; 5; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma708 : selectionSortDemo [4; 3; 1; 0; 2; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma709 : selectionSortDemo [4; 3; 1; 0; 5; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma710 : selectionSortDemo [4; 3; 1; 2; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma711 : selectionSortDemo [4; 3; 1; 2; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma712 : selectionSortDemo [4; 3; 1; 5; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma713 : selectionSortDemo [4; 3; 1; 5; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma714 : selectionSortDemo [4; 3; 2; 0; 1; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma715 : selectionSortDemo [4; 3; 2; 0; 5; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma716 : selectionSortDemo [4; 3; 2; 1; 0; 5] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma717 : selectionSortDemo [4; 3; 2; 1; 5; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma718 : selectionSortDemo [4; 3; 2; 5; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma719 : selectionSortDemo [4; 3; 2; 5; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma720 : selectionSortDemo [4; 3; 5; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma721 : selectionSortDemo [4; 3; 5; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma722 : selectionSortDemo [4; 3; 5; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma723 : selectionSortDemo [4; 3; 5; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma724 : selectionSortDemo [4; 3; 5; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma725 : selectionSortDemo [4; 3; 5; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma726 : selectionSortDemo [4; 5; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma727 : selectionSortDemo [4; 5; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma728 : selectionSortDemo [4; 5; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma729 : selectionSortDemo [4; 5; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma730 : selectionSortDemo [4; 5; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma731 : selectionSortDemo [4; 5; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma732 : selectionSortDemo [4; 5; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma733 : selectionSortDemo [4; 5; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma734 : selectionSortDemo [4; 5; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma735 : selectionSortDemo [4; 5; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma736 : selectionSortDemo [4; 5; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma737 : selectionSortDemo [4; 5; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma738 : selectionSortDemo [4; 5; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma739 : selectionSortDemo [4; 5; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma740 : selectionSortDemo [4; 5; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma741 : selectionSortDemo [4; 5; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma742 : selectionSortDemo [4; 5; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma743 : selectionSortDemo [4; 5; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma744 : selectionSortDemo [4; 5; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma745 : selectionSortDemo [4; 5; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma746 : selectionSortDemo [4; 5; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma747 : selectionSortDemo [4; 5; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma748 : selectionSortDemo [4; 5; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma749 : selectionSortDemo [4; 5; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma750 : selectionSortDemo [5; 0; 1; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma751 : selectionSortDemo [5; 0; 1; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma752 : selectionSortDemo [5; 0; 1; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma753 : selectionSortDemo [5; 0; 1; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma754 : selectionSortDemo [5; 0; 1; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma755 : selectionSortDemo [5; 0; 1; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma756 : selectionSortDemo [5; 0; 2; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma757 : selectionSortDemo [5; 0; 2; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma758 : selectionSortDemo [5; 0; 2; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma759 : selectionSortDemo [5; 0; 2; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma760 : selectionSortDemo [5; 0; 2; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma761 : selectionSortDemo [5; 0; 2; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma762 : selectionSortDemo [5; 0; 3; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma763 : selectionSortDemo [5; 0; 3; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma764 : selectionSortDemo [5; 0; 3; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma765 : selectionSortDemo [5; 0; 3; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma766 : selectionSortDemo [5; 0; 3; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma767 : selectionSortDemo [5; 0; 3; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma768 : selectionSortDemo [5; 0; 4; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma769 : selectionSortDemo [5; 0; 4; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma770 : selectionSortDemo [5; 0; 4; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma771 : selectionSortDemo [5; 0; 4; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma772 : selectionSortDemo [5; 0; 4; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma773 : selectionSortDemo [5; 0; 4; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma774 : selectionSortDemo [5; 1; 0; 2; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma775 : selectionSortDemo [5; 1; 0; 2; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma776 : selectionSortDemo [5; 1; 0; 3; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma777 : selectionSortDemo [5; 1; 0; 3; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma778 : selectionSortDemo [5; 1; 0; 4; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma779 : selectionSortDemo [5; 1; 0; 4; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma780 : selectionSortDemo [5; 1; 2; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma781 : selectionSortDemo [5; 1; 2; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma782 : selectionSortDemo [5; 1; 2; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma783 : selectionSortDemo [5; 1; 2; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma784 : selectionSortDemo [5; 1; 2; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma785 : selectionSortDemo [5; 1; 2; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma786 : selectionSortDemo [5; 1; 3; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma787 : selectionSortDemo [5; 1; 3; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma788 : selectionSortDemo [5; 1; 3; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma789 : selectionSortDemo [5; 1; 3; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma790 : selectionSortDemo [5; 1; 3; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma791 : selectionSortDemo [5; 1; 3; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma792 : selectionSortDemo [5; 1; 4; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma793 : selectionSortDemo [5; 1; 4; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma794 : selectionSortDemo [5; 1; 4; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma795 : selectionSortDemo [5; 1; 4; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma796 : selectionSortDemo [5; 1; 4; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma797 : selectionSortDemo [5; 1; 4; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma798 : selectionSortDemo [5; 2; 0; 1; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma799 : selectionSortDemo [5; 2; 0; 1; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma800 : selectionSortDemo [5; 2; 0; 3; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma801 : selectionSortDemo [5; 2; 0; 3; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma802 : selectionSortDemo [5; 2; 0; 4; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma803 : selectionSortDemo [5; 2; 0; 4; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma804 : selectionSortDemo [5; 2; 1; 0; 3; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma805 : selectionSortDemo [5; 2; 1; 0; 4; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma806 : selectionSortDemo [5; 2; 1; 3; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma807 : selectionSortDemo [5; 2; 1; 3; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma808 : selectionSortDemo [5; 2; 1; 4; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma809 : selectionSortDemo [5; 2; 1; 4; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma810 : selectionSortDemo [5; 2; 3; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma811 : selectionSortDemo [5; 2; 3; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma812 : selectionSortDemo [5; 2; 3; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma813 : selectionSortDemo [5; 2; 3; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma814 : selectionSortDemo [5; 2; 3; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma815 : selectionSortDemo [5; 2; 3; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma816 : selectionSortDemo [5; 2; 4; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma817 : selectionSortDemo [5; 2; 4; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma818 : selectionSortDemo [5; 2; 4; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma819 : selectionSortDemo [5; 2; 4; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma820 : selectionSortDemo [5; 2; 4; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma821 : selectionSortDemo [5; 2; 4; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma822 : selectionSortDemo [5; 3; 0; 1; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma823 : selectionSortDemo [5; 3; 0; 1; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma824 : selectionSortDemo [5; 3; 0; 2; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma825 : selectionSortDemo [5; 3; 0; 2; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma826 : selectionSortDemo [5; 3; 0; 4; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma827 : selectionSortDemo [5; 3; 0; 4; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma828 : selectionSortDemo [5; 3; 1; 0; 2; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma829 : selectionSortDemo [5; 3; 1; 0; 4; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma830 : selectionSortDemo [5; 3; 1; 2; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma831 : selectionSortDemo [5; 3; 1; 2; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma832 : selectionSortDemo [5; 3; 1; 4; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma833 : selectionSortDemo [5; 3; 1; 4; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma834 : selectionSortDemo [5; 3; 2; 0; 1; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma835 : selectionSortDemo [5; 3; 2; 0; 4; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma836 : selectionSortDemo [5; 3; 2; 1; 0; 4] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma837 : selectionSortDemo [5; 3; 2; 1; 4; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma838 : selectionSortDemo [5; 3; 2; 4; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma839 : selectionSortDemo [5; 3; 2; 4; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma840 : selectionSortDemo [5; 3; 4; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma841 : selectionSortDemo [5; 3; 4; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma842 : selectionSortDemo [5; 3; 4; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma843 : selectionSortDemo [5; 3; 4; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma844 : selectionSortDemo [5; 3; 4; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma845 : selectionSortDemo [5; 3; 4; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma846 : selectionSortDemo [5; 4; 0; 1; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma847 : selectionSortDemo [5; 4; 0; 1; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma848 : selectionSortDemo [5; 4; 0; 2; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma849 : selectionSortDemo [5; 4; 0; 2; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma850 : selectionSortDemo [5; 4; 0; 3; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma851 : selectionSortDemo [5; 4; 0; 3; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma852 : selectionSortDemo [5; 4; 1; 0; 2; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma853 : selectionSortDemo [5; 4; 1; 0; 3; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma854 : selectionSortDemo [5; 4; 1; 2; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma855 : selectionSortDemo [5; 4; 1; 2; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma856 : selectionSortDemo [5; 4; 1; 3; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma857 : selectionSortDemo [5; 4; 1; 3; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma858 : selectionSortDemo [5; 4; 2; 0; 1; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma859 : selectionSortDemo [5; 4; 2; 0; 3; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma860 : selectionSortDemo [5; 4; 2; 1; 0; 3] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma861 : selectionSortDemo [5; 4; 2; 1; 3; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma862 : selectionSortDemo [5; 4; 2; 3; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma863 : selectionSortDemo [5; 4; 2; 3; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma864 : selectionSortDemo [5; 4; 3; 0; 1; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma865 : selectionSortDemo [5; 4; 3; 0; 2; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma866 : selectionSortDemo [5; 4; 3; 1; 0; 2] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma867 : selectionSortDemo [5; 4; 3; 1; 2; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma868 : selectionSortDemo [5; 4; 3; 2; 0; 1] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.

Lemma selectionSortTestLemma869 : selectionSortDemo [5; 4; 3; 2; 1; 0] = [0; 1; 2; 3; 4; 5].
Proof.
  simpl. easy.
Qed.
