From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Observation Intern InternBounded InternGrowth FormulaEncoding Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module InternReserve.
Import IndexExecution SipHashExecution.
Theorem generated_refines s bs ns fs p reserve observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 ->
  Z.of_nat (length fs + S reserve) <= 9223372036854775807 ->
  FormulaEncoding.normal (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) ->
  FormulaEncoding.decode fs (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) = Some p ->
  exists final next index, execObserved (funcdef_0__intern bs ns) (s,observations) = Some (tt,(final,observations)) /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\
    meta_value final 8 = 0 /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some p /\ (exists extra, next = fs ++ extra) /\
    Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  intros Harena Herror Hreserve Hnormal Hdecode.
  assert (Hcapacity : Z.of_nat (length fs) <= 9223372036854775807) by (rewrite Nat2Z.inj_add in Hreserve; lia).
  destruct (InternBounded.generated_refines s bs ns fs p Harena Herror Hcapacity Hnormal Hdecode)
    as [final [next [index [Hrun [Hframe [Hflag [Hindex [Hword [Hnext [Hlookup Hextends]]]]]]]]]].
  pose proof (InternGrowth.at_most_one s final bs ns fs next Harena Herror Hcapacity Hrun Hnext) as Hgrowth.
  exists final,next,index. split; [apply observed_plain; [apply InternalObservation.intern_nf|exact Hrun]|].
  split; [exact Hframe|]. split; [exact Hnext|]. split; [exact Hflag|]. split; [exact Hindex|].
  split; [unfold word; lia|]. split; [exact Hlookup|]. split; [exact Hextends|].
  assert (Hmass : (length next + reserve <= length fs + S reserve)%nat) by lia. apply Nat2Z.inj_le in Hmass. lia.
Qed.
Lemma lookup_preserved {A} (fs next : list A) index value : (exists extra, next = fs ++ extra) ->
  nth_error fs index = Some value -> nth_error next index = Some value.
Proof. intros [extra ->] Hlookup. rewrite nth_error_app1; [exact Hlookup|apply nth_error_Some; congruence]. Qed.
Lemma extends_trans {A} (first middle last : list A) :
  (exists extra, middle = first ++ extra) -> (exists extra, last = middle ++ extra) -> exists extra, last = first ++ extra.
Proof. intros [a ->] [b ->]. exists (a++b). now rewrite app_assoc. Qed.
End InternReserve.
