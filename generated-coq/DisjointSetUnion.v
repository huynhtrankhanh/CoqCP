From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0__dsu
| arraydef_0__hasBeenInitialized
| arraydef_0__result.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0__dsu => Z | arraydef_0__hasBeenInitialized => Z | arraydef_0__result => Z end; arrays := fun name => match name with | arraydef_0__dsu => repeat (0%Z) 100 | arraydef_0__hasBeenInitialized => repeat (0%Z) 1 | arraydef_0__result => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__ancestor :=
| vardef_0__ancestor_vertex
| vardef_0__ancestor_work.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__ancestor : EqDecision varsfuncdef_0__ancestor := ltac:(solve_decision).
Definition funcdef_0__ancestor (bools : varsfuncdef_0__ancestor -> bool) (numbers : varsfuncdef_0__ancestor -> Z) (addresses : varsfuncdef_0__ancestor -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work) x) >>=
fun _ => ((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__dsu) x) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8))))) >>= fun x => if x then (
    (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__dsu) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__result) x y) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work) x) >>=
fun _ => ((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__dsu) x) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8))))) >>= fun x => if x then (
    (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__dsu) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_vertex) x)) >>=
  fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__result) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (arraydef_0__dsu) x y)) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__ancestor (vardef_0__ancestor_work) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__unite :=
| vardef_0__unite_u
| vardef_0__unite_v
| vardef_0__unite_z.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__unite : EqDecision varsfuncdef_0__unite := ltac:(solve_decision).
Definition funcdef_0__unite (bools : varsfuncdef_0__unite -> bool) (numbers : varsfuncdef_0__unite -> Z) (addresses : varsfuncdef_0__unite -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ancestor_vertex) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__ancestor y x z)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u) x) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ancestor_vertex) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__ancestor y x z)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v) x) >>=
fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun x => (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  (((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x) >>= fun a => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8)))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_z) x) >>=
    fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u) x) >>=
    fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_z)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v) x) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((addInt 8 (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x) (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x y) >>=
  fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x y) >>=
  fun _ => ((getSender _ _ _) >>= fun address => (((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (vardef_0__unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__unite (arraydef_0__dsu) x) >>= fun x => Done _ _ _ (coerceInt (-x) 8)) >>= fun x => Done _ _ _ (coerceInt x 256)) >>= fun money => donate _ _ _ money address) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__main : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__hasBeenInitialized) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__hasBeenInitialized) x y) >>=
  fun _ => ((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => ((((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt (-x) 64)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dsu) x y)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__unite_u) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__unite_v) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__unite y x z)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__result) x y) >>=
fun _ => Done _ _ _ tt).
