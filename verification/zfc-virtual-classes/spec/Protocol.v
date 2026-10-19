From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From Trusted Require Import SetTheory VirtualClasses Schemata.
From Stdlib Require Import Lists.List ZArith.ZArith Arith.PeanoNat.
From stdpp Require Import numbers list.
Import ListNotations SetTheory VirtualClasses.
Open Scope Z_scope.

Module Protocol.
Definition maximum := 18446744073709551615.
Definition name := list Z.
Definition name_eq_dec : forall a b : name, {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.
Record request := Req { opcode : nat; arguments : list nat; object_name : name }.
Inductive reply := OK (id : nat) | NO | CLASS | SET | THEOREM | SCHEMA | BYE | ERR.
Definition reply_bytes r := match r with
| OK i => [79;75;32] ++ decimalBytes i ++ [10]
| NO => [78;79;10] | CLASS => [67;76;65;83;83;10] | SET => [83;69;84;10]
| THEOREM => [84;72;69;79;82;69;77;10] | SCHEMA => [83;67;72;69;77;65;10]
| BYE => [66;89;69;10] | ERR => [69;82;82;10] end.
Definition valid_name n := (0 < length n <= 1024)%nat /\
  Forall (fun c => 0 <= c < 256 /\ c <> 32 /\ c <> 9 /\ c <> 10 /\ c <> 13) n.
Definition shape q :=
  Forall (fun n => Z.of_nat n <= maximum) (arguments q) /\
  match opcode q with
  | 0%nat | 16%nat | 17%nat => arguments q = [] /\ object_name q = []
  | 1%nat | 2%nat | 3%nat | 7%nat | 8%nat | 12%nat | 18%nat => length (arguments q) = 2%nat /\ object_name q = []
  | 4%nat | 5%nat | 6%nat | 13%nat | 19%nat => length (arguments q) = 1%nat /\ object_name q = []
  | 9%nat | 14%nat | 20%nat | 23%nat => length (arguments q) = 1%nat /\ valid_name (object_name q)
  | 10%nat | 15%nat | 21%nat | 25%nat | 26%nat => arguments q = [] /\ valid_name (object_name q)
  | 11%nat => length (arguments q) = 4%nat /\ object_name q = []
  | 22%nat => length (arguments q) = 5%nat /\ object_name q = []
  | 24%nat => valid_name (object_name q) /\ Z.of_nat (length (arguments q)) <= maximum
  | _ => False end.
Definition number_tokens ns := map decimalBytes ns.
Fixpoint join_tokens ts := match ts with [] => [] | [t] => t | t :: ts => t ++ [32] ++ join_tokens ts end.
Definition request_bytes q :=
  let op := decimalBytes (opcode q) in
  let fields := number_tokens (arguments q) in
  let n := object_name q in
  join_tokens (match opcode q with
  | 9%nat | 20%nat | 23%nat => op :: fields ++ [n]
  | 14%nat => op :: n :: fields
  | 10%nat | 15%nat | 21%nat | 25%nat | 26%nat => [op;n]
  | 24%nat => op :: n :: decimalBytes (length (arguments q)) :: fields
  | _ => op :: fields end) ++ [10].
Definition wire qs := concat (map request_bytes qs).
Definition seed_prompt : list Z := [83;69;69;68;10].
Definition ready_reply : list Z := [82;69;65;68;89;10].
Definition seed_bytes k0 k1 := join_tokens [decimalBytes k0;decimalBytes k1] ++ [10].
Definition handshake_output := seed_prompt ++ ready_reply.

Inductive expression := CE (c : Schemata.class_template)
  | FE (p : Schemata.formula_template) | PE (c : Schemata.proof_template).
Inductive binding := class_binding (id : nat) (certified : bool)
  | theorem_binding (formula_id : nat) | schema_binding (root : nat).
Record state := State {
  formulas : list formula; classes : list class; history : list nat;
  bindings : list (name * binding); expressions : list expression
}.
Definition initial := State [falsity] [] [] [] [].
Fixpoint lookup (n : name) (bs : list (name * binding)) : option binding := match bs with [] => None | (key,v) :: bs =>
  if name_eq_dec n key then Some v else lookup n bs end.
Definition with_history s hs := State (formulas s) (classes s) hs (bindings s) (expressions s).
Definition formula_at s i := nth_error (formulas s) i.
Definition theorem_at s i := match nth_error (history s) i with
  | Some f => formula_at s f | None => None end.
Definition class_at s i := nth_error (classes s) i.
Definition cf s i := match nth_error (expressions s) i with Some (CE c) => Some c | _ => None end.
Definition ff s i := match nth_error (expressions s) i with Some (FE p) => Some p | _ => None end.
Definition pf s i := match nth_error (expressions s) i with Some (PE c) => Some c | _ => None end.
Definition empty_template := Schemata.literal_formula falsity.
Definition formula_argument s (needed : bool) i := if needed then ff s i else Some empty_template.
Definition axiom_expression s tag a b c : option Schemata.proof_template :=
  let need_p := existsb (Nat.eqb tag) [0;1;2;3;4;15;16]%nat in
  let need_q := existsb (Nat.eqb tag) [0;1;4]%nat in
  match formula_argument s need_p a, formula_argument s need_q b,
        formula_argument s (Nat.eqb tag 1) c with
  | Some p, Some q, Some r => if Nat.leb tag 17 then
      Some (Schemata.template_ax (Schemata.template_axiom tag p q r a b c)) else None
  | _, _, _ => None end.

Inductive builds_node (s : state) : list nat -> expression -> Prop :=
| node_meta a b c d : Z.of_nat a < maximum -> builds_node s [0;a;b;c;d]%nat (CE (Schemata.metavariable a))
| node_class a b c d cls : class_at s a = Some cls -> builds_node s [1;a;b;c;d]%nat (CE (Schemata.literal_class cls))
| node_formula a b c d p : formula_at s a = Some p -> builds_node s [2;a;b;c;d]%nat (FE (Schemata.literal_formula p))
| node_abstract a b c d p : ff s a = Some p -> builds_node s [3;a;b;c;d]%nat (CE (Schemata.template_abstract p))
| node_equal a b c d x y : cf s a = Some x -> cf s b = Some y -> builds_node s [4;a;b;c;d]%nat (FE (Schemata.template_equal x y))
| node_member a b c d x y : cf s a = Some x -> cf s b = Some y -> builds_node s [5;a;b;c;d]%nat (FE (Schemata.template_member x y))
| node_imp a b c d p q : ff s a = Some p -> ff s b = Some q -> builds_node s [6;a;b;c;d]%nat (FE (Schemata.template_imp p q))
| node_all a b c d p : ff s a = Some p -> builds_node s [7;a;b;c;d]%nat (FE (Schemata.template_all p))
| node_ax tag a b c cert : axiom_expression s tag a b c = Some cert -> builds_node s [8;tag;a;b;c]%nat (PE cert)
| node_mp a b c d p q : pf s a = Some p -> pf s b = Some q -> builds_node s [9;a;b;c;d]%nat (PE (Schemata.template_mp p q))
| node_gen a b c d p : pf s a = Some p -> builds_node s [10;a;b;c;d]%nat (PE (Schemata.template_gen p))
| node_saved a b c d p (H : derives p) : theorem_at s a = Some p ->
    builds_node s [11;a;b;c;d]%nat (PE (Schemata.saved_theorem p H)).

Definition class_setness c := match c with
| set i => ex (equal 0 (S i))
| abstract _ => ex (all (SetTheory.iff (member 0 1) (predicate c (fun n => S (S n)) 0))) end.

Inductive formula_request s : request -> formula -> Prop :=
| req_equal i j : formula_request s (Req 1 [i;j] []) (equal i j)
| req_member i j : formula_request s (Req 2 [i;j] []) (member i j)
| req_imp i j p q : formula_at s i = Some p -> formula_at s j = Some q -> formula_request s (Req 3 [i;j] []) (implies p q)
| req_all i p : formula_at s i = Some p -> formula_request s (Req 4 [i] []) (all p)
| req_class_equal i j a b : class_at s i = Some a -> class_at s j = Some b -> formula_request s (Req 7 [i;j] []) (erase (class_equal a b))
| req_class_member i j a b : class_at s i = Some a -> class_at s j = Some b -> formula_request s (Req 8 [i;j] []) (erase (class_member a b)).

Definition concrete_axiom s tag a b c : option formula :=
  let get (needed : bool) i := if needed then option_map Schemata.literal_formula (formula_at s i) else Some empty_template in
  match get (existsb (Nat.eqb tag) [0;1;2;3;4;15;16]%nat) a,
        get (existsb (Nat.eqb tag) [0;1;4]%nat) b, get (Nat.eqb tag 1) c with
  | Some p, Some q, Some r => option_map axiom_formula
      (Schemata.instantiate_axiom (fun _ => set 0) 0 (Schemata.template_axiom tag p q r a b c))
  | _, _, _ => None end.

Inductive proof_request s : request -> formula -> Prop :=
| req_axiom tag a b c p : concrete_axiom s tag a b c = Some p -> proof_request s (Req 11 [tag;a;b;c] []) p
| req_mp i j p q : theorem_at s i = Some (implies p q) -> theorem_at s j = Some p -> proof_request s (Req 12 [i;j] []) q
| req_gen i p : theorem_at s i = Some p -> proof_request s (Req 13 [i] []) (all p)
| req_restate i j p : theorem_at s i = Some p -> formula_at s j = Some p -> proof_request s (Req 18 [i;j] []) p
| req_recall n i p : lookup n (bindings s) = Some (theorem_binding i) -> formula_at s i = Some p -> proof_request s (Req 21 [] n) p
| req_instance n root cert ids actual p : lookup n (bindings s) = Some (schema_binding root) ->
    pf s root = Some cert -> length ids = Schemata.proof_arity cert ->
    Forall2 (fun i c => class_at s i = Some c) ids actual ->
    Schemata.infer (fun i => List.nth i actual (set 0)) 0 cert = Some p ->
    proof_request s (Req 24 ids n) p.

(* Internal interning may allocate auxiliary subformulas and shifted classes.
   IDs already returned by the protocol must remain immutable and canonical. *)
Definition allocation s fs cs i p :=
  (exists extra, fs = formulas s ++ extra) /\ NoDup fs /\ nth_error fs i = Some p /\
  (exists extra, cs = classes s ++ extra).

Inductive accepted : state -> request -> reply -> state -> Prop :=
| accept_quit s : accepted s (Req 0 [] []) BYE s
| accept_formula s q p fs cs i : formula_request s q p -> allocation s fs cs i p ->
    accepted s q (OK i) (State fs cs (history s) (bindings s) (expressions s))
| accept_set s i : accepted s (Req 5 [i] []) (OK (length (classes s)))
    (State (formulas s) (classes s ++ [set i]) (history s) (bindings s) (expressions s))
| accept_abstract s i p : formula_at s i = Some p ->
    accepted s (Req 6 [i] []) (OK (length (classes s)))
      (State (formulas s) (classes s ++ [abstract (core p)]) (history s) (bindings s) (expressions s))
| accept_proof s q p fs cs i : proof_request s q p -> allocation s fs cs i p ->
    accepted s q (OK (length (history s)))
      (State fs cs (history s ++ [i]) (bindings s) (expressions s))
| accept_name_class s n i c : class_at s i = Some c -> lookup n (bindings s) = None ->
    accepted s (Req 9 [i] n) (OK i) (State (formulas s) (classes s) (history s)
      (bindings s ++ [(n,class_binding i false)]) (expressions s))
| accept_name_theorem s n i f : nth_error (history s) i = Some f -> lookup n (bindings s) = None ->
    accepted s (Req 20 [i] n) (OK f) (State (formulas s) (classes s) (history s)
      (bindings s ++ [(n,theorem_binding f)]) (expressions s))
| accept_name_schema s n root cert : pf s root = Some cert -> lookup n (bindings s) = None ->
    accepted s (Req 23 [root] n) (OK root) (State (formulas s) (classes s) (history s)
      (bindings s ++ [(n,schema_binding root)]) (expressions s))
| accept_lookup s n i flag : lookup n (bindings s) = Some (class_binding i flag) -> accepted s (Req 10 [] n) (OK i) s
| accept_query s n i flag : lookup n (bindings s) = Some (class_binding i flag) ->
    accepted s (Req 15 [] n) (if flag then SET else CLASS) s
| accept_certify s n i cls flag index : lookup n (bindings s) = Some (class_binding i flag) ->
    class_at s i = Some cls -> theorem_at s index = Some (class_setness cls) ->
    accepted s (Req 14 [index] n) (OK i) (State (formulas s) (classes s) (history s)
      (map (fun item => if name_eq_dec n (fst item) then (n,class_binding i true) else item) (bindings s)) (expressions s))
| accept_undo s hs last : history s = hs ++ [last] -> accepted s (Req 16 [] []) (OK (length hs)) (with_history s hs)
| accept_reset s : accepted s (Req 17 [] []) (OK 0) (with_history s [])
| accept_inspect s i f : nth_error (history s) i = Some f -> accepted s (Req 19 [i] []) (OK f) s
| accept_node s args e : builds_node s args e -> accepted s (Req 22 args []) (OK (length (expressions s)))
    (State (formulas s) (classes s) (history s) (bindings s) (expressions s ++ [e]))
| accept_kind_class s n i flag : lookup n (bindings s) = Some (class_binding i flag) -> accepted s (Req 25 [] n) CLASS s
| accept_kind_theorem s n i : lookup n (bindings s) = Some (theorem_binding i) -> accepted s (Req 25 [] n) THEOREM s
| accept_kind_schema s n i : lookup n (bindings s) = Some (schema_binding i) -> accepted s (Req 25 [] n) SCHEMA s
| accept_arity s n root cert : lookup n (bindings s) = Some (schema_binding root) -> pf s root = Some cert ->
    accepted s (Req 26 [] n) (OK (Schemata.proof_arity cert)) s.

(* Expanding a class, setness query or rejected certificate can cache syntax.
   This storage is retained even when no theorem or binding is committed. *)
Definition retained_storage s t :=
  (exists extra, formulas t = formulas s ++ extra) /\ NoDup (formulas t) /\
  (exists extra, classes t = classes s ++ extra) /\
  history t = history s /\ bindings t = bindings s /\ expressions t = expressions s.
Inductive step s q : reply -> state -> Prop :=
| step_accept r t u : accepted s q r t -> retained_storage t u -> step s q r u
| step_reject t : (forall r u, ~ accepted s q r u) -> retained_storage s t -> step s q NO t.

(* A schedule specifies each flush's cumulative output and still-unread input.
   Quit consumes its request, replies once, and leaves the suffix unread. *)
Inductive dialogue : state -> list request -> list reply -> state -> list Z -> Prop :=
| dialogue_eof s : dialogue s [] [] s []
| dialogue_quit s tail : dialogue s (Req 0 [] [] :: tail) [BYE] s (wire tail)
| dialogue_step s q tail r t rs final remaining : opcode q <> 0%nat -> step s q r t ->
    dialogue t tail rs final remaining -> dialogue s (q :: tail) (r :: rs) final remaining.
Fixpoint flush_schedule qs rs prefix : list FlushSnapshot := match qs,rs with
| q :: tail,r :: rest =>
    let output := prefix ++ reply_bytes r in
    {| flushedOutput := output; unreadInput := wire tail |} :: flush_schedule tail rest output
| _,_ => [] end.

(* Arithmetic/resource safety is a separate explicit domain condition; this
   contract still requires termination, complete replies, and every flush. *)
Section EndToEnd.
Context {I : Type} {T : I -> Type} `{EqDecision I}.
Definition required (program : Action (WithArrays I T) withArraysReturnValue unit)
  (initial_memory : forall name, list (T name)) (within_capacity : list request -> Prop) :=
  forall k0 k1 qs, Z.of_nat k0 <= maximum -> Z.of_nat k1 <= maximum ->
  Forall shape qs -> within_capacity qs ->
  exists rs final logical remaining,
    dialogue initial qs rs logical remaining /\
    execObserved program
      ({| memory := initial_memory; stdin := seed_bytes k0 k1 ++ wire qs; stdout := [] |}, []) =
      Some (tt,(final,
        {| flushedOutput := seed_prompt; unreadInput := seed_bytes k0 k1 ++ wire qs |} ::
        {| flushedOutput := handshake_output; unreadInput := wire qs |} ::
        flush_schedule qs rs handshake_output)) /\
    stdout final = handshake_output ++ concat (map reply_bytes rs) /\ stdin final = remaining.
End EndToEnd.
End Protocol.
