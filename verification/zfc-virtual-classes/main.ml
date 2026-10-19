(* Text transport for the extracted Gallina state machine. The kernel checks
   every submitted typed object; this parser and printer are not verified. *)
open Checker
open Checker.SetTheory
open Checker.VirtualClasses

type sexp = Atom of string | List of sexp list
exception Parse_error of string
let fail message = raise (Parse_error message)

let parse text =
  let length = String.length text in
  let rec skip i =
    if i < length && (text.[i] = ' ' || text.[i] = '\t' || text.[i] = '\r')
    then skip (i + 1) else i
  in
  let rec expression i =
    let i = skip i in
    if i = length then fail "expected an expression";
    match text.[i] with
    | ')' -> fail "unexpected closing parenthesis"
    | '(' -> sequence (i + 1) []
    | _ ->
        let rec finish j =
          if j = length || List.mem text.[j] [' '; '\t'; '\r'; '('; ')']
          then j else finish (j + 1)
        in
        let j = finish i in Atom (String.sub text i (j - i)), j
  and sequence i acc =
    let i = skip i in
    if i = length then fail "unclosed parenthesis";
    if text.[i] = ')' then List (List.rev acc), i + 1
    else let item, j = expression i in sequence j (item :: acc)
  in
  let result, last = expression 0 in
  if skip last <> length then fail "trailing input";
  result

let natural = function
  | Atom value when String.length value > 0 &&
      String.for_all (fun c -> c >= '0' && c <= '9') value ->
      Big_int_Z.big_int_of_string value
  | _ -> fail "expected a nonnegative decimal index"

let rec formula = function
  | Atom "false" -> Coq_falsity
  | List [Atom "="; i; j] -> Coq_equal (natural i, natural j)
  | List [Atom "in"; i; j] -> Coq_member (natural i, natural j)
  | List [Atom "imp"; p; q] -> Coq_implies (formula p, formula q)
  | List [Atom "all"; p] -> Coq_all (formula p)
  | List [Atom "not"; p] -> neg (formula p)
  | List [Atom "and"; p; q] -> conj (formula p) (formula q)
  | List [Atom "or"; p; q] -> disj (formula p) (formula q)
  | List [Atom "iff"; p; q] -> iff (formula p) (formula q)
  | List [Atom "exists"; p] -> ex (formula p)
  | _ -> fail "invalid core formula"

let rec statement = function
  | List [Atom "core"; p] -> Coq_core (formula p)
  | List [Atom "=>"; p; q] -> Coq_implication (statement p, statement q)
  | List [Atom "forall"; p] -> Coq_universal (statement p)
  | List [Atom "class="; a; b] -> Coq_class_equal (class_term a, class_term b)
  | List [Atom "class-in"; a; b] -> Coq_class_member (class_term a, class_term b)
  | p -> Coq_core (formula p)
and class_term = function
  | List [Atom "set"; i] -> Coq_set (natural i)
  | List [Atom "class"; body] -> Coq_abstract (statement body)
  | _ -> fail "expected (set index) or (class statement)"

let axiom = function
  | Atom "ext" -> Ext | Atom "found" -> Found | Atom "pair" -> Pair
  | Atom "union" -> Union | Atom "power" -> Power | Atom "infinity" -> Infinity
  | Atom "choice" -> Choice
  | List [Atom "k"; p; q] -> K (formula p, formula q)
  | List [Atom "s"; p; q; r] -> Srule (formula p, formula q, formula r)
  | List [Atom "dne"; p] -> DNE (formula p)
  | List [Atom "inst"; p; j] -> Inst (formula p, natural j)
  | List [Atom "dist"; p; q] -> Dist (formula p, formula q)
  | List [Atom "refl"; i] -> Refl (natural i)
  | List [Atom "mem-left"; i; j; k] -> MemLeft (natural i, natural j, natural k)
  | List [Atom "mem-right"; i; j; k] -> MemRight (natural i, natural j, natural k)
  | List [Atom "eq-trans"; i; j; k] -> EqTrans (natural i, natural j, natural k)
  | List [Atom "sep"; p] -> Separation (formula p)
  | List [Atom "repl"; p] -> Replacement (formula p)
  | _ -> fail "invalid axiom witness"

let rec certificate = function
  | List [Atom "ax"; a] -> Axiom_use (axiom a)
  | List [Atom "ref"; i] -> Reference (natural i)
  | List [Atom "mp"; implication; antecedent] ->
      Modus_ponens (certificate implication, certificate antecedent)
  | List [Atom "gen"; proof] -> Generalize (certificate proof)
  | _ -> fail "invalid proof certificate"

let rec print_formula = function
  | Coq_falsity -> "false"
  | Coq_equal (i, j) -> Printf.sprintf "(= %s %s)"
      (Big_int_Z.string_of_big_int i) (Big_int_Z.string_of_big_int j)
  | Coq_member (i, j) -> Printf.sprintf "(in %s %s)"
      (Big_int_Z.string_of_big_int i) (Big_int_Z.string_of_big_int j)
  | Coq_implies (p, q) -> Printf.sprintf "(imp %s %s)" (print_formula p) (print_formula q)
  | Coq_all p -> Printf.sprintf "(all %s)" (print_formula p)

let () =
  let history = ref [] in
  let dispatch command =
    let accepted, next = Implementation.program !history command in
    history := next;
    Printf.printf "%s %d\n%!" (if accepted then "OK" else "REJECT") (List.length next)
  in
  let rec loop () =
    match input_line stdin with
    | line ->
        let line = String.trim line in
        if line = "quit" then ()
        else begin
          (try
             if line <> "" && line.[0] <> ';' then
               match parse line with
               | Atom "undo" -> dispatch Undo
               | Atom "reset" -> dispatch Reset
               | Atom "show" ->
                   List.iteri (fun i p -> Printf.printf "%d %s\n" i (print_formula (erase p))) !history;
                   flush stdout
               | List [Atom "expand"; p] -> Printf.printf "%s\n%!" (print_formula (erase (statement p)))
               | List [Atom "axiom"; a] ->
                   let a = axiom a in dispatch (Submit (Coq_core (axiom_formula a), Axiom_use a))
               | List [Atom "prove"; p; proof] -> dispatch (Submit (statement p, certificate proof))
               | _ -> fail "expected prove, axiom, expand, show, undo, reset or quit"
           with
           | Parse_error message -> Printf.printf "ERROR %s\n%!" message
           | Stack_overflow -> Printf.printf "ERROR expression too deep\n%!"
           | Invalid_argument message -> Printf.printf "ERROR %s\n%!" message);
          loop ()
        end
    | exception End_of_file -> ()
  in
  loop ()
