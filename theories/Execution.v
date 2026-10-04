From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality.

Section Execution.
Context {I : Type} {T : I -> Type} `{EqDecision I}.
Record Machine := {
  memory : forall name, list (T name);
  stdin : list Z;
  stdout : list Z
}.
Definition withMemory (s : Machine) m := {| memory := m; stdin := stdin s; stdout := stdout s |}.
Definition withInput (s : Machine) input := {| memory := memory s; stdin := input; stdout := stdout s |}.
Definition withOutput (s : Machine) output := {| memory := memory s; stdin := stdin s; stdout := output |}.
Definition optionBind {A B} (x : option A) (f : A -> option B) :=
  match x with Some value => f value | None => None end.
Definition step (e : WithArrays I T) (s : Machine) : option (withArraysReturnValue e * Machine) :=
  match e with
  | DoBasicEffect _ _ Trap => None
  | DoBasicEffect _ _ Flush => Some (tt, s)
  | DoBasicEffect _ _ ReadChar =>
      match stdin s with
      | [] => Some ((2^64 - 1)%Z, s)
      | x :: xs => Some (x, withInput s xs)
      end
  | DoBasicEffect _ _ (WriteChar x) => Some (tt, withOutput s (stdout s ++ [x]))
  | Retrieve _ _ name index =>
      match decide (Nat.lt (Z.to_nat index) (length (memory s name))) with
      | left h => Some (nth_lt (memory s name) (Z.to_nat index) h, s)
      | right _ => None
      end
  | Store _ _ name index value =>
      if decide (Nat.lt (Z.to_nat index) (length (memory s name)))
      then Some (tt, withMemory s (modifyArray (memory s) name (Z.to_nat index) value))
      else None
  | Grow _ _ name size zero => Some (tt, withMemory s (growArrays (memory s) name (Z.to_nat size) zero))
  end.
Fixpoint exec {R} (code : Action (WithArrays I T) withArraysReturnValue R) (s : Machine) : option (R * Machine) :=
  match code with
  | Done _ _ _ value => Some (value, s)
  | Dispatch _ _ _ e next => optionBind (step e s) (fun response => exec (next (fst response)) (snd response))
  end.
Lemma exec_bind {A B} (code : Action (WithArrays I T) withArraysReturnValue A)
  (next : A -> Action (WithArrays I T) withArraysReturnValue B) s :
  exec (code >>= next) s = optionBind (exec code s) (fun response => exec (next (fst response)) (snd response)).
Proof.
  induction code as [value | e cont IH] in s |- *; simpl; [reflexivity |].
  destruct (step e s) as [[x s'] |]; simpl; [apply IH | reflexivity].
Qed.

Section Locals.
Context {V : Type} `{EqDecision V}.
Record Frame := { machine : Machine; bools : V -> bool; nums : V -> Z }.
Definition setMachine (f : Frame) s := {| machine := s; bools := bools f; nums := nums f |}.
Definition setBool (f : Frame) name value := {| machine := machine f; bools := update (bools f) name value; nums := nums f |}.
Definition setNum (f : Frame) name value := {| machine := machine f; bools := bools f; nums := update (nums f) name value |}.
Definition localStep (e : WithLocalVariables I T V) (f : Frame) : option (withLocalVariablesReturnValue e * Frame) :=
  match e with
  | DoWithArrays _ _ _ e => optionBind (step e (machine f)) (fun response => Some (fst response, setMachine f (snd response)))
  | BooleanLocalGet _ _ _ name => Some (bools f name, f)
  | BooleanLocalSet _ _ _ name value => Some (tt, setBool f name value)
  | NumberLocalGet _ _ _ name => Some (nums f name, f)
  | NumberLocalSet _ _ _ name value => Some (tt, setNum f name value)
  end.
Fixpoint execLocal {R} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue R)
  (f : Frame) : option (R * Frame) :=
  match code with
  | Done _ _ _ value => Some (value, f)
  | Dispatch _ _ _ e next => optionBind (localStep e f) (fun response => execLocal (next (fst response)) (snd response))
  end.
Lemma execLocal_bind {A B} (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue A)
  (next : A -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue B) f :
  execLocal (code >>= next) f = optionBind (execLocal code f) (fun response => execLocal (next (fst response)) (snd response)).
Proof.
  induction code as [value | e cont IH] in f |- *; simpl; [reflexivity |].
  destruct (localStep e f) as [[x f'] |]; simpl; [apply IH | reflexivity].
Qed.
Lemma exec_eliminate (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit) b n s :
  exec (eliminateLocalVariables b n code) s =
  optionBind (execLocal code {| machine := s; bools := b; nums := n |})
    (fun response => Some (fst response, machine (snd response))).
Proof.
  induction code as [value | e cont IH] in b, n, s |- *; [reflexivity |].
  destruct e as [effect | name | name value | name | name value]; simpl.
  - destruct (step effect s) as [[x s'] |]; simpl; [apply IH | reflexivity].
  - apply IH.
  - apply IH.
  - apply IH.
  - apply IH.
Qed.
Lemma execLocal_lift {R} (code : Action (WithArrays I T) withArraysReturnValue R) f :
  execLocal (liftToWithLocalVariables code) f =
  optionBind (exec code (machine f)) (fun response => Some (fst response, setMachine f (snd response))).
Proof.
  induction code as [value | e cont IH] in f |- *.
  - destruct f; reflexivity.
  - simpl. destruct (step e (machine f)) as [[x s'] |]; simpl; [| reflexivity].
    rewrite IH. cbn [machine setMachine]. destruct (exec (cont x) s') as [[y s''] |]; [destruct f |]; reflexivity.
Qed.
End Locals.

Lemma exec_runProgram (code : Action (WithArrays I T) withArraysReturnValue unit) values input output :
  runIO (getNewArrays code values) input output =
  optionBind (exec code {| memory := values; stdin := input; stdout := output |})
    (fun response => let s := snd response in Some (memory s, stdin s, stdout s)).
Proof.
  induction code as [value | e cont IH] in values, input, output |- *; [reflexivity |].
  destruct e as [e | name index | name index value | name size zero]; simpl.
  - destruct e; simpl; try apply IH; [reflexivity |].
    destruct input; simpl; apply IH.
  - destruct (decide (Nat.lt (Z.to_nat index) (length (values name)))); simpl; [apply IH | reflexivity].
  - destruct (decide (Nat.lt (Z.to_nat index) (length (values name)))); simpl; [apply IH | reflexivity].
  - apply IH.
Qed.
End Execution.

Fixpoint arrayLoop {I T} (count : nat) (body : nat -> Action (WithArrays I T) withArraysReturnValue unit) :=
  match count with
  | O => Done _ _ _ tt
  | S n => body n >>= fun _ => arrayLoop n body
  end.
Lemma liftToWithLocalVariables_bind {I T V A B}
  (code : Action (WithArrays I T) withArraysReturnValue A)
  (next : A -> Action (WithArrays I T) withArraysReturnValue B) :
  @liftToWithLocalVariables I T V B (code >>= next) =
  liftToWithLocalVariables code >>= fun x => liftToWithLocalVariables (next x).
Proof.
  induction code as [value | e cont IH]; simpl; [reflexivity |].
  f_equal. apply functional_extensionality. apply IH.
Qed.
Lemma loop_lift {I T V} count (body : nat -> Action (WithArrays I T) withArraysReturnValue unit) :
  loop count (fun n => @liftToWithLocalVariables I T V unit (body n) >>= fun _ => Done _ _ _ KeepGoing) =
  liftToWithLocalVariables (arrayLoop count body).
Proof.
  induction count as [| count IH]; simpl; [reflexivity |].
  rewrite <- bindAssoc.
  cbn [bind].
  rewrite IH.
  symmetry. apply liftToWithLocalVariables_bind.
Qed.

Lemma eliminate_arrayLoop {I T V} `{EqDecision V} b nums count
  (body : nat -> Action (WithLocalVariables I T V) withLocalVariablesReturnValue LoopOutcome)
  (code : nat -> Action (WithArrays I T) withArraysReturnValue unit)
  (hBody : forall index continuation,
    eliminateLocalVariables b nums (body index >>= continuation) =
    code index >>= fun _ => eliminateLocalVariables b nums (continuation KeepGoing))
  continuation :
  eliminateLocalVariables b nums (loop count body >>= continuation) =
  arrayLoop count code >>= fun _ => eliminateLocalVariables b nums (continuation tt).
Proof.
  induction count as [| count IH]; simpl; [reflexivity |].
  rewrite <- bindAssoc. rewrite hBody. cbn [bind]. rewrite IH.
  apply bindAssoc.
Qed.

Lemma bind_unit_identity {E R} (code : Action E R unit) :
  code >>= (fun _ => Done _ _ _ tt) = code.
Proof.
  replace (fun _ : unit => Done E R unit tt) with (Done E R unit).
  - apply rightIdentity.
  - apply functional_extensionality. intros []; reflexivity.
Qed.

Lemma arrayLoop_ext {I T} count
  (left right : nat -> Action (WithArrays I T) withArraysReturnValue unit)
  (h : forall index, (index < count)%nat -> left index = right index) :
  arrayLoop count left = arrayLoop count right.
Proof.
  induction count as [| count IH]; [reflexivity |].
  cbn [arrayLoop]. rewrite h; [| lia].
  f_equal. apply functional_extensionality. intro x. apply IH. intros; apply h; lia.
Qed.

Lemma transport_bind {E F A B X Y} (h : X = Y)
  (code : X -> Action E F A) (next : A -> Action E F B) y :
  eq_rect X (fun t => t -> Action E F B) (fun x => code x >>= next) Y h y =
  eq_rect X (fun t => t -> Action E F A) code Y h y >>= next.
Proof. destruct h. reflexivity. Qed.

Lemma translateArrays_bind {I J T A B}
  (code : Action (WithArrays I T) withArraysReturnValue A)
  (next : A -> Action (WithArrays I T) withArraysReturnValue B)
  U (mapping : I -> J) congruent :
  translateArrays (code >>= next) U mapping congruent =
  translateArrays code U mapping congruent >>= fun value => translateArrays (next value) U mapping congruent.
Proof.
  induction code as [value | e cont IH]; [reflexivity |].
  destruct e as [effect | name index | name index value | name size zero]; cbn [bind translateArrays Action_rect].
  all: f_equal; apply functional_extensionality; intro response.
  all: try apply IH.
  change (eq_rect (T name) (fun t => t -> Action (WithArrays J U) withArraysReturnValue B)
    (fun x => translateArrays (cont x >>= next) U mapping congruent)
    (U (mapping name)) (congruent name) response =
    eq_rect (T name) (fun t => t -> Action (WithArrays J U) withArraysReturnValue A)
      (fun x => translateArrays (cont x) U mapping congruent)
      (U (mapping name)) (congruent name) response >>=
    fun value => translateArrays (next value) U mapping congruent).
  assert (functions : (fun x => translateArrays (cont x >>= next) U mapping congruent) =
    (fun x => translateArrays (cont x) U mapping congruent >>= fun value => translateArrays (next value) U mapping congruent)).
  { apply functional_extensionality. apply IH. }
  transitivity (eq_rect (T name) (fun t => t -> Action (WithArrays J U) withArraysReturnValue B)
    (fun x => translateArrays (cont x) U mapping congruent >>= fun value => translateArrays (next value) U mapping congruent)
    (U (mapping name)) (congruent name) response).
  - apply (f_equal (fun function => eq_rect (T name) (fun t => t -> Action (WithArrays J U) withArraysReturnValue B)
      function (U (mapping name)) (congruent name) response)). exact functions.
  - apply transport_bind.
Qed.

Lemma translate_arrayLoop {I J T} count
  (body : nat -> Action (WithArrays I T) withArraysReturnValue unit)
  U (mapping : I -> J) congruent :
  translateArrays (arrayLoop count body) U mapping congruent =
  arrayLoop count (fun index => translateArrays (body index) U mapping congruent).
Proof.
  induction count as [| count IH]; [reflexivity |].
  cbn [arrayLoop]. rewrite translateArrays_bind.
  f_equal. apply functional_extensionality. intros []. exact IH.
Qed.
