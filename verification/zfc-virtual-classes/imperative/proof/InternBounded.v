From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashScan InternTail HashTable Rehash Rebuild RehashFull ScanFrame InternCore InternInvariant Intern FormulaEncoding Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module InternBounded.
Import IndexExecution SipHashExecution HashScanExecution InternTailExecution HashTableInvariant
  RehashExecution RebuildExecution RehashFullExecution InternCoreExecution InternInvariant InternExecution.
Local Opaque hash_tuple funcdef_0__formulaHash funcdef_0__rehashFormulas after_resize after_scan.
Theorem generated_intern_bounded s bs ns n : table s n -> meta_value s 8 = 0 -> Z.of_nat n <= 9223372036854775807 ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\
    logical_frame s final /\
    canonical s final n
      (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b).
Proof.
  intros Htable Hflag Hbound.
  pose proof Htable as [Hready [Hcount [Hsizeword [Hbucketlen [Hload [Hindexed Hunique]]]]]].
  pose proof Hready as [Hm [Hs [Hp [Hcapacity [Hformulas [Hlinks Hlimit]]]]]].
  set (f := {| machine := s; bools := bs; nums := ns |}).
  set (f0 := setNum f vardef_0__intern_found 0).
  unfold funcdef_0__intern. rewrite exec_eliminate, InternCoreExecution.actual_body. fold f.
  destruct (Z_lt_dec (Z.of_nat n) (meta_value s 20)) as [Hstrict|Hfull].
  - rewrite (skip_resize funcdef_0__rehashFormulas funcdef_0__formulaHash f ltac:(change (20 < length (memory s arraydef_0__meta))%nat; lia) ltac:(change (meta_value s 1 <> meta_value s 20); lia)).
    destruct (generated_lookup f0 n Htable Hstrict Hflag ltac:(reflexivity)) as [last [Hrun [Hframe Hpost]]].
    fold f0. rewrite Hrun. cbn [optionBind fst snd]. exists (machine last). split; [reflexivity|]. split; [exact Hframe|]. exact Hpost.
  - assert (Hsize : meta_value s 20 = Z.of_nat n) by lia.
    assert (Hpositive : (0 < n)%nat) by lia.
    assert (Hlength : (length (memory s arraydef_0__formulaBuckets) <= 2*n)%nat).
    { rewrite Hbucketlen, Hsize, Nat2Z.id. lia. }
    destruct (Z_le_dec (Z.of_nat n) 9223372036854775807) as [Hsmall|Hoverflow].
    + destruct (generated_rehash_small s (fun _ => false) (fun _ => 0) n n Hm Hs Hsize Hpositive Hlength Hcount
        Hsmall Hformulas Hlinks Hlimit) as [resized [Hresize Hpost]].
      rewrite (run_resize funcdef_0__rehashFormulas funcdef_0__formulaHash f resized ltac:(change (20 < length (memory s arraydef_0__meta))%nat; lia)
        ltac:(change (meta_value s 1 = meta_value s 20); lia) Hresize).
      assert (Hnewtable : table resized n) by (apply (rehash_table s resized n n); try assumption; lia).
      pose proof Hpost as [_ [_ [_ [Hnewsize [Hcells [Ha Hio]]]]]].
      assert (Hnewstrict : Z.of_nat n < meta_value resized 20) by (rewrite Hnewsize; lia).
      assert (Hnewflag : meta_value resized 8 = 0) by (rewrite Hcells by lia; exact Hflag).
      destruct (generated_lookup (setMachine f0 resized) n Hnewtable Hnewstrict Hnewflag ltac:(reflexivity))
        as [last [Hrun [Hframe Hcanonical]]].
      fold f0. rewrite Hrun. cbn [optionBind fst snd]. exists (machine last). split; [reflexivity|]. split.
      * apply (logical_trans _ resized); [now apply (rehash_logical s resized n n)|exact Hframe].
      * apply (canonical_source s resized); [now apply Ha|exact Hcanonical].
    + lia.
Qed.
Theorem generated_refines s bs ns meaning p :
  NativeRepresentation.canonical_arena s meaning -> meta_value s 8 = 0 ->
  Z.of_nat (length meaning) <= 9223372036854775807 ->
  FormulaEncoding.normal (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
  FormulaEncoding.decode meaning (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) = Some p ->
  exists final next index,
    exec (funcdef_0__intern bs ns) s = Some (tt,final) /\ logical_frame s final /\
    meta_value final 8 = 0 /\ meta_value final 0 = Z.of_nat index /\ Z.of_nat index <= maximum /\
    NativeRepresentation.canonical_arena final next /\ nth_error next index = Some p /\
    exists extra, next = meaning ++ extra.
Proof.
  intros Harena Herror Hbound Hnormal Hdecode.
  destruct (generated_intern_bounded s bs ns (length meaning) (proj1 Harena) Herror Hbound)
    as [final [Hrun [Hframe Hcanonical]]].
  pose proof (NativeRepresentation.canonical_semantics s final meaning
    (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) p Harena Hnormal Hdecode Hcanonical)
    as [next [Hnext [Hlookup Hextends]]].
  destruct Hcanonical as [Hflag [count [index [Hcount [Htable [Hindex [Hresult _]]]]]]].
  assert (Hword : Z.of_nat index <= maximum).
  { destruct (proj1 Htable) as [_ [_ [_ [_ [_ [_ Hlimit]]]]]]. lia. }
  exists final,next,index. split; [exact Hrun|]. split; [exact Hframe|].
  split; [exact Hflag|]. split; [exact Hresult|]. split; [exact Hword|]. split; [exact Hnext|].
  split; [rewrite Hresult, Nat2Z.id in Hlookup; exact Hlookup|exact Hextends].
Qed.
End InternBounded.
