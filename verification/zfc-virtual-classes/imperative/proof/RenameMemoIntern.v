From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern InternInvariant InternBounded InternLengths FormulaEncoding Representation
  RenameMemoTable RenameMemoLookup RenameMemoInvariant RenameMemoMeaning Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoIntern.
Import IndexExecution SipHashExecution.
Local Opaque hash_state siphash24.
Theorem preserved s t count meaning : RenameMemoInvariant.valid s count meaning -> InternExecution.logical_frame s t ->
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) ->
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) ->
  0<meta_value t 20 -> meta_value t 8=0 -> RenameMemoInvariant.valid t count meaning.
Proof.
  intros Hvalid [Ha [Hm [Hi Ho]]] Hmeta Hsip Hpositive Herror.
  assert (Htable : RenameMemoLookup.table t=RenameMemoLookup.table s).
  { unfold RenameMemoLookup.table. now rewrite Ha by discriminate. }
  assert (Hhash : forall query, RenameMemoLookup.hash_start t query count=RenameMemoLookup.hash_start s query count).
  { intro query. unfold RenameMemoLookup.hash_start. now rewrite !Hm by lia. }
  destruct Hvalid as [Hmeta0 Hsip0 Hpositive0 Herror0 Hcapacity Hminimum Hword Hallocated Hlive Hload Hmeaning Hindexed].
  constructor.
  - now rewrite Hmeta.
  - now rewrite Hsip.
  - exact Hpositive.
  - exact Herror.
  - now rewrite Hm by lia.
  - exact Hminimum.
  - exact Hword.
  - now rewrite Ha by discriminate.
  - now rewrite Hm,Htable by lia.
  - now rewrite Hm by lia.
  - now rewrite Htable.
  - intros index Hindex Hoccupied. rewrite Htable in Hoccupied |- *. rewrite Hhash. now apply Hindexed.
Qed.
Theorem extended s count fs next rho : RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning fs rho) ->
  (exists extra, next=fs++extra) -> RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning next rho).
Proof.
  intros [Hmeta Hsip Hpositive Herror Hcapacity Hminimum Hword Hallocated Hlive Hload Hmeaning Hindexed] [extra ->].
  constructor; try assumption. exact (RenameMemoMeaning.table_extends (RenameMemoLookup.table s) count fs extra rho Hmeaning).
Qed.
Theorem generated s bs ns fs source count rho observations :
  RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena s fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  FormulaEncoding.normal (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
  FormulaEncoding.decode fs (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b)=Some source ->
  exists final next index, execObserved (funcdef_0__intern bs ns) (s,observations)=Some (tt,(final,observations)) /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\
    RenameMemoInvariant.valid final count (RenameMemoMeaning.entry_meaning next rho) /\
    meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\ nth_error next index=Some source /\
    (exists extra, next=fs++extra).
Proof.
  intros Hvalid Harena Hcapacity Hnormal Hdecode.
  destruct (InternBounded.generated_refines s bs ns fs source Harena (RenameMemoInvariant.error_clear _ _ _ Hvalid) Hcapacity Hnormal Hdecode)
    as [final [next [index [Hrun [Hframe [Herror [Hindex [Hword [Hnext [Hlookup Hextends]]]]]]]]]].
  assert (Hobserved : execObserved (funcdef_0__intern bs ns) (s,observations)=Some (tt,(final,observations))).
  { apply observed_plain; [apply InternalObservation.intern_nf|exact Hrun]. }
  destruct (InternLengths.observed_lengths s bs ns observations final observations Hobserved) as [Hmeta Hsip].
  pose proof (proj1 (proj1 Hnext)) as [_ [_ [Hpositive _]]].
  assert (Hcache : RenameMemoInvariant.valid final count (RenameMemoMeaning.entry_meaning next rho)).
  { apply extended with (fs:=fs); [|exact Hextends]. exact (preserved s final count _ Hvalid Hframe Hmeta Hsip Hpositive Herror). }
  exists final,next,index. split; [exact Hobserved|]. split; [exact Hframe|]. split; [exact Hnext|]. split; [exact Hcache|].
  split; [exact Hindex|]. split; [unfold word; lia|]. split; assumption.
Qed.
End RenameMemoIntern.
