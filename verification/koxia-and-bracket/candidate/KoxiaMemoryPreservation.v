From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaArrays KoxiaModular KoxiaRoots KoxiaFourier KoxiaSizes KoxiaTables KoxiaTableLoops KoxiaNTT KoxiaConvolution KoxiaArrayLoops KoxiaConvolutionExecution KoxiaConvolutionCorrect KoxiaConvolutionReady.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Local Opaque stageRoot stageInverse modularPower.
Lemma withArray_lengths (state : @Machine arrayIndex1 (arrayType _ environment1)) name replacement :
  length replacement=length (memory state name) -> forall other,
  length (memory (withArray state name replacement) other)=length (memory state other).
Proof.
  intros sameLength other. destruct (decide (other=name)) as [->|different].
  - rewrite withArray_preserve_same. exact sameLength.
  - rewrite withArray_preserve_other by exact different. reflexivity.
Qed.
Lemma withResult_lengths state value name : length (memory (withResult state value) name)=length (memory state name).
Proof. unfold withResult. apply withArray_lengths. apply length_insert. Qed.
Theorem convolutionFinal_lengths stage count state len cut span base name :
  length (memory (convolutionFinal stage count state len cut span base) name)=length (memory state name).
Proof.
  unfold convolutionFinal.
  rewrite withArray_lengths by apply fillValues_length.
  rewrite <-withArray_work. rewrite withArray_lengths.
  2: rewrite convolutionOutput_length,withArray_preserve_other,withResult_other by congruence; reflexivity.
  rewrite withArray_lengths by (rewrite convolutionOther_length,withResult_lengths; reflexivity).
  apply withResult_lengths.
Qed.
Theorem readyConvolution_preserves state len cut span base name :
  name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
  memory (readyConvolutionFinal state len cut span base) name=memory state name.
Proof. unfold readyConvolutionFinal. apply convolutionFinal_preserves. Qed.
Theorem readyConvolution_canonical state len cut span base :
  ConvolutionReady state len cut span base -> tableCanonical (memory state arraydef_0__arena) ->
  tableCanonical (memory (readyConvolutionFinal state len cut span base) arraydef_0__work) /\
  tableCanonical (memory (readyConvolutionFinal state len cut span base) arraydef_0__other) /\
  tableCanonical (memory (readyConvolutionFinal state len cut span base) arraydef_0__arena).
Proof.
  intros ready arenaCanonical.
  destruct ready as [polyRoom lengthBound countBound arenaFit workRoom otherRoom rootsRoom workFit rootsFit factRoom inverseRoom factorial inverse workCanonical otherCanonical rootsCanonical polyCanonical resultRoom arenaRoom rootsCorrect].
  set (stage := ceilingStage 20 (Z.of_nat (len-cut+span)) 0).
  pose proof (convolution_models_canonical stage state len cut span workRoom ltac:(lia) workCanonical otherCanonical polyCanonical)
    as [inputCanonical [firstCanonical [copiedCanonical [kernelCanonical [secondCanonical [productCanonical [negatedCanonical outputCanonical]]]]]]].
  unfold readyConvolutionFinal,convolutionFinal. fold stage. split.
  - rewrite withArray_preserve_other by congruence. rewrite withWork_memory. exact outputCanonical.
  - split.
    + rewrite withArray_preserve_other by congruence. rewrite withWork_other by congruence.
      rewrite withArray_preserve_same. exact copiedCanonical.
    + rewrite withArray_preserve_same. apply fillValues_canonical; [exact arenaCanonical|].
      intros index indexBound. apply tableCanonical_nth; [exact outputCanonical|].
      rewrite convolutionOutput_length. pose proof (ceilingStage_correct (Z.of_nat (len-cut+span)) ltac:(lia)) as [bound sizes].
      fold stage in workRoom,sizes. rewrite stageSize_nat in sizes. cbn [arrayType environment1] in *. lia.
Qed.
Lemma readyConvolution_arena_prefix state len cut span base index :
  ConvolutionReady state len cut span base -> (index<base)%nat ->
  nth index (memory (readyConvolutionFinal state len cut span base) arraydef_0__arena) 0=
  nth index (memory state arraydef_0__arena) 0.
Proof.
  intros ready below. unfold readyConvolutionFinal,convolutionFinal. rewrite withArray_preserve_same.
  rewrite fillValues_lookup by exact (ready_arena_room state len cut span base ready).
  rewrite bool_decide_false by lia. reflexivity.
Qed.
