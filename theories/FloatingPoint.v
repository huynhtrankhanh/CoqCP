(** Deterministic scalar WebAssembly floating point.  SpecFloat is part of
    Rocq itself; in particular its NaN constructor has no sign or payload. *)
From Stdlib Require Import Floats.SpecFloat.
From stdpp Require Import countable.
From CoqCP Require Import Options Imperative.
Local Open Scope Z_scope.

Inductive floatFormat := Binary32 | Binary64.
Definition floatPrecision f : Z := match f with Binary32 => 24 | Binary64 => 53 end.
Definition floatEmax f : Z := match f with Binary32 => 128 | Binary64 => 1024 end.
Definition floatWidth f : Z := match f with Binary32 => 32 | Binary64 => 64 end.
Record floatValue (f : floatFormat) := FloatValue { floatSpec : spec_float }.
Arguments FloatValue {_} _.
Arguments floatSpec {_} _.
Global Instance specFloatDecision : EqDecision spec_float.
Proof. solve_decision. Defined.
Global Instance floatDecision f : EqDecision (floatValue f).
Proof. solve_decision. Defined.
Definition specFloatCode (v : spec_float) : nat * bool * positive * Z :=
  match v with
  | S754_zero s => (0%nat,s,1%positive,0)
  | S754_infinity s => (1%nat,s,1%positive,0)
  | S754_nan => (2%nat,false,1%positive,0)
  | S754_finite s m e => (3%nat,s,m,e)
  end.
Definition specFloatDecode (v : nat * bool * positive * Z) : spec_float :=
  let '(tag,s,m,e) := v in
  match tag with
  | 0%nat => S754_zero s | 1%nat => S754_infinity s
  | 2%nat => S754_nan | _ => S754_finite s m e
  end.
Global Instance specFloatCountable : Countable spec_float.
Proof.
  apply (inj_countable' specFloatCode specFloatDecode). intros []; reflexivity.
Defined.
Global Instance floatCountable f : Countable (floatValue f).
Proof. apply (inj_countable' floatSpec (@FloatValue f)). intros []; reflexivity. Defined.
Definition floatZero f : floatValue f := FloatValue (S754_zero false).
Definition floatEncode {f} (v : floatValue f) : Z := encode_Z v.
Definition floatDecode f (z : Z) : floatValue f := default (floatZero f) (decode_Z z).
Lemma floatDecode_encode f (v : floatValue f) : floatDecode f (floatEncode v) = v.
Proof. unfold floatDecode, floatEncode. rewrite decode_encode_Z. reflexivity. Qed.
Lemma floatDecode_default f : floatDecode f 0 = floatZero f.
Proof. reflexivity. Qed.

Definition floatFromFields f (s : bool) (ex frac : Z) : floatValue f :=
  let fracBits := floatPrecision f - 1 in
  let expBits := floatWidth f - floatPrecision f in
  FloatValue (if ex =? 2^expBits-1 then
    if frac =? 0 then S754_infinity s else S754_nan
  else if ex =? 0 then
    if frac =? 0 then S754_zero s
    else S754_finite s (Z.to_pos frac) (3-floatEmax f-floatPrecision f)
  else S754_finite s (Z.to_pos (2^fracBits+frac)) (ex-(floatEmax f-1)-fracBits)).
Definition floatFromBits f (bits : Z) : floatValue f :=
  let fracBits := floatPrecision f - 1 in
  let expBits := floatWidth f - floatPrecision f in
  floatFromFields f (Z.testbit bits (floatWidth f - 1))
    (Z.land (Z.shiftr bits fracBits) (2^expBits-1))
    (Z.land bits (2^fracBits-1)).
Definition floatValid {f} (x : floatValue f) : bool :=
  valid_binary (floatPrecision f) (floatEmax f) (floatSpec x).
Lemma floatNaN_fields f sign payload :
  payload <> 0 ->
  floatFromFields f sign (2^(floatWidth f-floatPrecision f)-1) payload =
    FloatValue S754_nan.
Proof.
  intros h. unfold floatFromFields. rewrite Z.eqb_refl.
  apply Z.eqb_neq in h. rewrite h. reflexivity.
Qed.
Definition floatNeg {f} (x : floatValue f) : floatValue f := FloatValue (SFopp (floatSpec x)).
Definition floatAbs {f} (x : floatValue f) : floatValue f := FloatValue (SFabs (floatSpec x)).
Definition floatAdd {f} (x y : floatValue f) : floatValue f :=
  FloatValue (SFadd (floatPrecision f) (floatEmax f) (floatSpec x) (floatSpec y)).
Definition floatSub {f} (x y : floatValue f) : floatValue f :=
  FloatValue (SFsub (floatPrecision f) (floatEmax f) (floatSpec x) (floatSpec y)).
Definition floatMul {f} (x y : floatValue f) : floatValue f :=
  FloatValue (SFmul (floatPrecision f) (floatEmax f) (floatSpec x) (floatSpec y)).
Definition floatDiv {f} (x y : floatValue f) : floatValue f :=
  FloatValue (SFdiv (floatPrecision f) (floatEmax f) (floatSpec x) (floatSpec y)).
Definition floatSqrt {f} (x : floatValue f) : floatValue f :=
  FloatValue (SFsqrt (floatPrecision f) (floatEmax f) (floatSpec x)).
Definition floatEq {f} (x y : floatValue f) := SFeqb (floatSpec x) (floatSpec y).
Definition floatNe {f} (x y : floatValue f) := negb (floatEq x y).
Definition floatLt {f} (x y : floatValue f) := SFltb (floatSpec x) (floatSpec y).
Definition floatLe {f} (x y : floatValue f) := SFleb (floatSpec x) (floatSpec y).
Definition floatGt {f} (x y : floatValue f) := floatLt y x.
Definition floatGe {f} (x y : floatValue f) := floatLe y x.
Definition floatMin {f} (x y : floatValue f) : floatValue f :=
  match floatSpec x, floatSpec y with
  | S754_nan, _ | _, S754_nan => FloatValue S754_nan
  | S754_zero s, S754_zero t => FloatValue (S754_zero (orb s t))
  | _, _ => if floatLt x y then x else y
  end.
Definition floatMax {f} (x y : floatValue f) : floatValue f :=
  match floatSpec x, floatSpec y with
  | S754_nan, _ | _, S754_nan => FloatValue S754_nan
  | S754_zero s, S754_zero t => FloatValue (S754_zero (andb s t))
  | _, _ => if floatLt x y then y else x
  end.
Definition floatOfZ f (z : Z) : floatValue f :=
  FloatValue (binary_normalize (floatPrecision f) (floatEmax f) z 0 false).
Definition floatConvertInt f (width : Z) (signed : bool) (z : Z) : floatValue f :=
  let u := z mod 2^width in
  floatOfZ f (if signed && (2^(width-1) <=? u) then u-2^width else u).
Definition floatCast target {source} (x : floatValue source) : floatValue target :=
  FloatValue (match floatSpec x with
    | S754_finite s m e => binary_round (floatPrecision target) (floatEmax target) s m e
    | v => v end).
(** mode: 0 trunc, 1 ceil, 2 floor, 3 nearest/ties-to-even. *)
Definition floatRound {f} (mode : Z) (x : floatValue f) : floatValue f :=
  match floatSpec x with
  | S754_finite s m e =>
    if 0 <=? e then x else
    let n := Z.pos m in let d := 2^(-e) in
    let q := n / d in let r := n mod d in
    let increment :=
      if mode =? 1 then negb s && negb (r =? 0) else
      if mode =? 2 then s && negb (r =? 0) else
      if mode =? 3 then (d <? 2*r) || ((d =? 2*r) && Z.odd q) else false in
    let magnitude := q + (if increment then 1 else 0) in
    if magnitude =? 0 then FloatValue (S754_zero s) else
    floatOfZ f (if s then -magnitude else magnitude)
  | _ => x end.
Definition floatTrunc {f} := @floatRound f 0.
Definition floatCeil {f} := @floatRound f 1.
Definition floatFloor {f} := @floatRound f 2.
Definition floatNearest {f} := @floatRound f 3.
Definition floatTruncatedZ {f} (x : floatValue f) : option Z :=
  match floatSpec x with
  | S754_zero _ => Some 0
  | S754_finite s m e =>
    let n := Z.shiftl (Z.pos m) e in Some (if s then -n else n)
  | _ => None end.
Definition floatTruncInt {f} (width : Z) (signed : bool) (x : floatValue f) : option Z :=
  let lo := if signed then -(2^(width-1)) else 0 in
  let hi := if signed then 2^(width-1)-1 else 2^width-1 in
  match floatTruncatedZ x with
  | Some z => if (lo <=? z) && (z <=? hi) then Some (z mod 2^width) else None
  | None => None end.
Definition floatTruncSatInt {f} (width : Z) (signed : bool) (x : floatValue f) : Z :=
  let lo := if signed then -(2^(width-1)) else 0 in
  let hi := if signed then 2^(width-1)-1 else 2^width-1 in
  (match floatTruncatedZ x with
  | Some z => Z.max lo (Z.min hi z)
  | None => match floatSpec x with S754_infinity s => if s then lo else hi | _ => 0 end
  end) mod 2^width.

Definition floatLocalGet f arrayIndex arrayType variableIndex name :=
  numberLocalGet arrayIndex arrayType variableIndex name >>=
    fun z => Done _ _ _ (floatDecode f z).
Definition floatLocalSet {f} arrayIndex arrayType variableIndex name (v : floatValue f) :=
  numberLocalSet arrayIndex arrayType variableIndex name (floatEncode v).
Definition floatTruncIntAction {f} arrayIndex arrayType variableIndex (width : Z) (signed : bool) (x : floatValue f) :=
  match floatTruncInt width signed x with
  | Some z => Done _ _ _ z
  | None => trap arrayIndex arrayType variableIndex Z
  end.

(** Payloads and signs of every input NaN are erased at the boundary. *)
Lemma floatNaN_unordered f (x : floatValue f) :
  floatEq (FloatValue S754_nan) x = false /\
  floatLt (FloatValue S754_nan) x = false /\
  floatLe (FloatValue S754_nan) x = false.
Proof. destruct x as [[]]; simpl; auto. Qed.
Example floatNaN32_erasure :
  floatFromBits Binary32 2143289345 = floatFromBits Binary32 4294967295.
Proof. vm_compute. reflexivity. Qed.
Example floatNaN64_erasure :
  floatFromBits Binary64 9221120237041090561 = floatFromBits Binary64 18446744073709551615.
Proof. vm_compute. reflexivity. Qed.
Example floatNearest_tie : floatNearest (floatFromBits Binary32 1075838976) = floatOfZ Binary32 2.
Proof. vm_compute. reflexivity. Qed.

Lemma floatTruncNaN f width signed :
  floatTruncInt (f:=f) width signed (FloatValue S754_nan) = None.
Proof. reflexivity. Qed.
Lemma floatTruncInt_range f width signed (x : floatValue f) n :
  0 < width -> floatTruncInt width signed x = Some n -> 0 <= n < 2^width.
Proof.
  intros hwidth. unfold floatTruncInt.
  destruct (floatTruncatedZ x) as [z|]; [| discriminate].
  destruct (_ && _); [| discriminate].
  intros h. inversion h; subst. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma eliminate_float_roundtrip {I T V} `{EqDecision V}
  f (b : V -> bool) (nums : V -> Z) name (v : floatValue f)
  (next : floatValue f -> Action (WithLocalVariables I T V)
    withLocalVariablesReturnValue unit) :
  eliminateLocalVariables b nums
    (floatLocalSet I T V name v >>= fun _ =>
     floatLocalGet f I T V name >>= next) =
  eliminateLocalVariables b (update nums name (floatEncode v)) (next v).
Proof.
  unfold floatLocalSet, floatLocalGet.
  cbn [numberLocalSet numberLocalGet bind].
  rewrite pushNumberSet, pushNumberGet.
  rewrite lookupSame, floatDecode_encode. reflexivity.
Qed.
