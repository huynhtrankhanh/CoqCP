From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashScan InternTail HashTable Rehash Rebuild RehashFull ScanFrame InternCore InternInvariant.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternExecution.
Import IndexExecution SipHashExecution HashScanExecution InternTailExecution HashTableInvariant
  RehashExecution RebuildExecution RehashFullExecution InternCoreExecution InternInvariant.
Definition Frame := HashScanExecution.Frame.
Definition logical_frame (s t : Machine) :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
    name <> arraydef_0__formulas -> name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets -> memory t name = memory s name) /\
  (forall i, i <> 0%nat -> i <> 1%nat -> i <> 8%nat -> i <> 20%nat -> i <> 21%nat -> i <> 28%nat -> meta_value t i = meta_value s i) /\
  stdin t = stdin s /\ stdout t = stdout s.
Definition canonical (s t : Machine) n tuple := meta_value t 8 = 0 /\
  exists count index, (count = n \/ (count = S n /\ index = n)) /\ table t count /\ (index < count)%nat /\
    meta_value t 0 = Z.of_nat index /\ tuple_at t index = tuple /\
    forall i, (i < n)%nat -> tuple_at t i = tuple_at s i.
Lemma logical_refl s : logical_frame s s.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma logical_trans s t u : logical_frame s t -> logical_frame t u -> logical_frame s u.
Proof.
  intros [Ha [Hc [Hi Ho]]] [Ha' [Hc' [Hi' Ho']]].
  split; [intros; now rewrite Ha', Ha by assumption|]. split; [intros; now rewrite Hc', Hc by assumption|]. split; congruence.
Qed.
Lemma stable_logical s t : stable s t -> logical_frame s t.
Proof. intros [Ha [_ [_ [Hc [Hi Ho]]]]]. split; [intros; now apply Ha|]. split; [intros; now apply Hc|]. split; assumption. Qed.
Lemma append_logical s n b tuple : logical_frame s (append_state s n b tuple).
Proof. split; [intros; now apply append_other|]. split; [intros; now apply append_meta_other|]. apply append_io. Qed.
Lemma rehash_logical s t size n : rehashed s t size n -> logical_frame s t.
Proof. intros [_ [_ [_ [_ [Hc [Ha [Hi Ho]]]]]]]. split; [intros; now apply Ha|]. split; [intros; now apply Hc|]. split; assumption. Qed.
Lemma canonical_source s r t n tuple : memory r arraydef_0__formulas = memory s arraydef_0__formulas ->
  canonical r t n tuple -> canonical s t n tuple.
Proof.
  intros Harray [Hflag [count [index [Hcount [Htable [Hi [Hr [Ht Hprefix]]]]]]]].
  split; [exact Hflag|]. exists count,index. split; [exact Hcount|]. split; [exact Htable|]. split; [exact Hi|].
  split; [exact Hr|]. split; [exact Ht|]. intros i Hbound. rewrite Hprefix by exact Hbound. unfold tuple_at. now rewrite Harray.
Qed.
Lemma scan_sought f hashed b p : sought (scan_start (setMachine f hashed) b p) = sought f.
Proof. destruct f. reflexivity. Qed.
Lemma generated_query (f : Frame) n : ready (machine f) n ->
  exec (funcdef_0__formulaHash (fun _ => false) (query_arguments f)) (machine f) =
    Some (tt,hash_tuple (machine f) (sought f)).
Proof. intros [Hm [Hs [Hp _]]]. unfold query_arguments, hash_tuple, sought. apply generated_hash; assumption. Qed.

Local Opaque hash_tuple funcdef_0__formulaHash funcdef_0__rehashFormulas after_resize after_scan.

Theorem generated_lookup (f : Frame) n : table (machine f) n ->
  Z.of_nat n < meta_value (machine f) 20 -> meta_value (machine f) 8 = 0 -> nums f vardef_0__intern_found = 0 ->
  exists final, execLocal (after_resize funcdef_0__formulaHash) f = Some (tt,final) /\
    logical_frame (machine f) (machine final) /\ canonical (machine f) (machine final) n (sought f).
Proof.
  intros Htable Hstrict Hflag Hfound.
  pose proof Htable as [Hready [Hcount [Hsizeword [Hbucketlen [Hload [Hindexed Hunique]]]]]].
  pose proof Hready as [Hm [Hs [Hp [Hcapacity [Hformulas [Hlinks Hlimit]]]]]].
  set (hashed := hash_tuple (machine f) (sought f)).
  assert (Hhashstable : stable (machine f) hashed) by apply hash_stable.
  pose proof (stable_table _ _ n Hhashstable Htable) as Hhashedtable.
  pose proof Hhashedtable as [Hhashedready [Hhashedcount [_ [_ [_ [Hhashedindexed _]]]]]].
  pose proof Hhashedready as [Hhashedmeta [_ [_ [_ [_ [_ Hhashedlimit]]]]]].
  set (bucket := keyed_bucket (machine f) (sought f)).
  assert (Hb : (bucket < length (memory hashed arraydef_0__formulaBuckets))%nat).
  { destruct Hhashstable as [Ha _]. rewrite Ha by discriminate. now apply (bucket_bound _ n). }
  destruct Hhashedindexed as [Hvalid [Hheads Hentries]].
  pose proof (Hheads bucket Hb) as Hhead.
  set (pointer := Z.to_nat (head_at hashed bucket)).
  assert (Hpointerbound : (pointer <= n)%nat).
  { pose proof (Z2Nat.id (head_at hashed bucket) ltac:(lia)). unfold pointer. lia. }
  set (start := scan_start (setMachine f hashed) bucket pointer).
  assert (Hstartpointer : nums start vardef_0__intern_current = Z.of_nat pointer) by reflexivity.
  assert (Hstartfound : nums start vardef_0__intern_found = 0) by (change (nums f vardef_0__intern_found = 0); exact Hfound).
  assert (Hstartmeta : (0 < length (memory (machine start) arraydef_0__meta))%nat)
    by (change (0 < length (memory hashed arraydef_0__meta))%nat; lia).
  destruct (scan_loop_checked n start n pointer Hvalid Hlimit Hstartmeta Hstartpointer Hpointerbound Hstartfound)
    as [last [Hscan [Hstorage Hchecked]]].
  pose proof (ScanFrameExecution.generated_scan_frame n start n pointer last Hvalid Hlimit Hstartmeta
    Hstartpointer Hpointerbound Hscan) as Hscanframe.
  assert (HscanStable : stable hashed (machine last)) by (apply (scan_stable start); assumption).
  pose proof (stable_trans _ _ _ Hhashstable HscanStable) as Hstable.
  pose proof (stable_table _ _ n Hstable Htable) as Hlasttable.
  destruct Hscanframe as [Hmetalen [Hlocals Hbools]].
  assert (Hlastsought : sought last = sought f).
  { unfold sought. rewrite (Hlocals vardef_0__intern_tag), (Hlocals vardef_0__intern_a), (Hlocals vardef_0__intern_b) by discriminate.
    apply scan_sought. }
  assert (Hlastbucket : nums last vardef_0__intern_bucket = Z.of_nat bucket).
  { rewrite Hlocals by discriminate. reflexivity. }
  assert (Hlastkey : bucket = keyed_bucket (machine last) (sought last)).
  { rewrite Hlastsought, (stable_key _ _ Hstable). reflexivity. }
  pose proof Hstable as [Harrays [Hml [Hsl [Hcells [Hin Hout]]]]].
  assert (Hlastflag : meta_value (machine last) 8 = 0) by (rewrite Hcells by lia; exact Hflag).
  assert (Hlaststrict : Z.of_nat n < meta_value (machine last) 20) by (rewrite Hcells by lia; exact Hstrict).
  pose proof (proj1 Hlasttable) as Hlastready.
  pose proof Hlastready as [Hlastmeta _].
  assert (Hlastbound : (bucket < length (memory (machine last) arraydef_0__formulaBuckets))%nat).
  { destruct HscanStable as [Ha _]. rewrite Ha by discriminate. exact Hb. }
  assert (Hpipeline : execLocal (after_resize funcdef_0__formulaHash) f = execLocal after_scan last).
  { rewrite (after_resize_live _ f hashed ltac:(lia) Hflag (generated_query f n Hready)).
    rewrite actual_after_hash.
    rewrite (after_hash_composition scan_callback _ n bucket pointer).
    - unfold scan_callback. rewrite Nat2Z.id. fold start. rewrite Hscan. reflexivity.
    - cbn [machine setMachine]. lia.
    - apply hash_bucket_value; assumption.
    - exact Hhashedcount.
    - exact Hb.
    - change (head_at hashed bucket = Z.of_nat pointer). unfold pointer. rewrite Z2Nat.id by lia. reflexivity. }
  destruct Hchecked as [Hmiss|[index [Hi [Hhit [Hresult Htuple]]]]].
  - assert (Hfresh : forall i, (i < n)%nat -> tuple_at (machine last) i <> sought last).
    { intros i Hi. rewrite Hlastsought. unfold tuple_at. rewrite Harrays by discriminate.
      assert (HindexedStart : indexed (machine start) n (keyed_bucket hashed)).
      { split; [exact Hvalid|]. split; [exact Hheads|exact Hentries]. }
      assert (HkeyStart : keyed_bucket hashed (sought start) = bucket).
      { change (keyed_bucket hashed (sought (scan_start (setMachine f hashed) bucket pointer)) = bucket).
        rewrite scan_sought, (stable_key _ _ Hhashstable). reflexivity. }
      assert (Hsp : nums start vardef_0__intern_current =
        Z.of_nat (Z.to_nat (head_at (machine start) (keyed_bucket hashed (sought start))))).
      { rewrite HkeyStart. exact Hstartpointer. }
      assert (Hsb : (keyed_bucket hashed (sought start) < length (memory (machine start) arraydef_0__formulaBuckets))%nat).
      { rewrite HkeyStart. exact Hb. }
      pose proof (scan_miss_absent start n (keyed_bucket hashed) last HindexedStart Hlimit Hstartmeta Hsp Hsb Hscan Hmiss i Hi) as Htuple.
      unfold tuple_at in Htuple. change (List.nth i (memory hashed arraydef_0__formulas) (0,0,0) <> sought start) in Htuple.
      destruct Hhashstable as [Ha _]. rewrite Ha in Htuple by discriminate.
      change (List.nth i (memory (machine f) arraydef_0__formulas) (0,0,0) <> sought f) in Htuple. exact Htuple. }
    pose proof (after_scan_fresh last n bucket ltac:(lia) (proj1 (proj2 Hlasttable)) ltac:(lia) Hmiss Hlastbucket Hlastbound) as Htail.
    set (fresh := setMachine last (append_state (machine last) n bucket (sought last))).
    exists fresh. split; [rewrite Hpipeline; exact Htail|]. split.
    + apply (logical_trans _ (machine last)); [now apply stable_logical|apply append_logical].
    + split; [change (meta_value (append_state (machine last) n bucket (sought last)) 8 = 0); now rewrite append_meta_other by lia|].
      exists (S n),n. split; [right; split; reflexivity|]. split.
      * change (table (append_state (machine last) n bucket (sought last)) (S n)). rewrite Hlastkey. now apply append_table.
      * split; [lia|]. split; [apply append_result; lia|]. split.
        -- change (tuple_at (append_state (machine last) n bucket (sought last)) n = sought f).
           unfold tuple_at. rewrite append_formula_new. exact Hlastsought.
        -- intros i Hi. change (tuple_at (append_state (machine last) n bucket (sought last)) i = tuple_at (machine f) i).
           unfold tuple_at. rewrite append_formula_previous by (try assumption; destruct Hlastready as [_ [_ [_ [_ [Hlen _]]]]]; lia).
           now rewrite Harrays by discriminate.
  - assert (Htail : execLocal after_scan last = Some (tt,last)).
    { apply after_scan_found. rewrite Hhit. discriminate. }
    exists last. split; [exact (eq_trans Hpipeline Htail)|]. split; [now apply stable_logical|].
    split; [exact Hlastflag|]. exists n,index. split; [now left|]. split; [exact Hlasttable|]. split; [exact Hi|].
    split; [exact Hresult|]. split.
    + unfold tuple_at. destruct Hstorage as [Ha _]. rewrite Ha by discriminate. rewrite Htuple. apply scan_sought.
    + intros i _. unfold tuple_at. now rewrite Harrays by discriminate.
Qed.

Lemma rehash_table s t size n : table s n -> rehashed s t size n ->
  Z.of_nat size <= 9223372036854775807 -> (n <= 2*size)%nat -> table t n.
Proof.
  intros [_ [Hcount [_ [_ [_ [_ Hunique]]]]]] [Hready [Hindexed [Hlen [Hsize [Hcells [Harray Hio]]]]]] Hlimit Hload.
  split; [exact Hready|]. split; [rewrite Hcells by lia; exact Hcount|].
  rewrite Hsize. split; [unfold maximum; lia|]. split; [rewrite Nat2Z.id; exact Hlen|].
  split; [lia|]. split; [exact Hindexed|].
  unfold unique, tuple_at in *. intros i j Hi Hj Heq. rewrite Harray in Heq by discriminate. now apply Hunique.
Qed.
Lemma fatal_logical s : logical_frame s (store_meta s 8 1).
Proof.
  split; [intros; now apply store_meta_other|]. split; [intros; now apply meta_store_other|]. split; reflexivity.
Qed.

Theorem generated_intern_correct s bs ns n : table s n -> meta_value s 8 = 0 ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\
    logical_frame s final /\
    (meta_value final 8 <> 0 \/ canonical s final n
      (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b)).
Proof.
  intros Htable Hflag.
  pose proof Htable as [Hready [Hcount [Hsizeword [Hbucketlen [Hload [Hindexed Hunique]]]]]].
  pose proof Hready as [Hm [Hs [Hp [Hcapacity [Hformulas [Hlinks Hlimit]]]]]].
  set (f := {| machine := s; bools := bs; nums := ns |}).
  set (f0 := setNum f vardef_0__intern_found 0).
  unfold funcdef_0__intern. rewrite exec_eliminate, InternCoreExecution.actual_body. fold f.
  destruct (Z_lt_dec (Z.of_nat n) (meta_value s 20)) as [Hstrict|Hfull].
  - rewrite (skip_resize funcdef_0__rehashFormulas funcdef_0__formulaHash f ltac:(change (20 < length (memory s arraydef_0__meta))%nat; lia) ltac:(change (meta_value s 1 <> meta_value s 20); lia)).
    destruct (generated_lookup f0 n Htable Hstrict Hflag ltac:(reflexivity)) as [last [Hrun [Hframe Hpost]]].
    fold f0. rewrite Hrun. cbn [optionBind fst snd]. exists (machine last). split; [reflexivity|]. split; [exact Hframe|]. right. exact Hpost.
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
      * right. apply (canonical_source s resized); [now apply Ha|exact Hcanonical].
    + assert (Hresize : exec (funcdef_0__rehashFormulas (fun _ => false) (fun _ => 0)) s = Some (tt,store_meta s 8 1)).
      { apply generated_rehash_full; [lia|lia]. }
      rewrite (run_resize funcdef_0__rehashFormulas funcdef_0__formulaHash f (store_meta s 8 1)
        ltac:(change (20 < length (memory s arraydef_0__meta))%nat; lia)
        ltac:(change (meta_value s 1 = meta_value s 20); lia) Hresize).
      rewrite after_resize_error.
      * cbn [optionBind fst snd]. exists (store_meta s 8 1). split; [reflexivity|]. split; [apply fatal_logical|].
        left. rewrite meta_store_same by lia. discriminate.
      * change (8 < length (memory (store_meta s 8 1%Z) arraydef_0__meta))%nat. rewrite store_meta_length. lia.
      * change (meta_value (store_meta s 8 1) 8 <> 0). rewrite meta_store_same by lia. discriminate.
Qed.
End InternExecution.
