(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state 
    let empty = failwith "Not implemented"*)
 	let empty = 
		let fail x = failwith (Printf.sprintf "Undefined variable: %s" x)
 		in {g = fail; l = fail; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    
    let update x v s = failwith "Not implemented"*)
	let update x v s = let update' f y = if x = y then v else f y
		in if List.mem x s.scope then {s with l = update' s.l} else {s with g = update' s.g}
                                
    (* Evals a variable in a state w.r.t. a scope 
    let eval s x = failwith "Not implemented" *)
	let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state 
    let enter st xs = failwith "Not implemented"*)
	let enter st xs = 
		let fail x = failwith (Printf.sprintf "Undefined variable: %s" x)
		in {g = st.g; l = fail; scope = xs}

    (* Drops a scope 
    let leave st st' = failwith "Not implemented"*)
	let leave st st' = {st with g = st'.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
                                                         
    let eval st expr = failwith "Not implemented"    *)
	let rec calc_bin bin x y = 
	let int_to_bool x = 
		if x = 0 then false else true
	and bool_to_int op_bool x y =
		if op_bool x y then 1 else 0
	in
	match bin with
	| "+" -> x + y
	| "-" -> x - y
	| "*" -> x * y
	| "/" -> x / y
	| "%" -> x mod y
	| "<" -> bool_to_int (<) x y
	| "<=" -> bool_to_int (<=) x y
	| ">" -> bool_to_int (>) x y
	| ">=" -> bool_to_int (>=) x y
	| "==" -> bool_to_int (==) x y
	| "!=" -> bool_to_int (<>) x y
	| "&&" -> bool_to_int (&&) (int_to_bool x) (int_to_bool y)
	| "!!" -> bool_to_int (||) (int_to_bool x) (int_to_bool y)
	| _ -> failwith (Printf.sprintf "Unknown bin op %s" bin)

	let rec eval st expr = 
		match expr with
		| Const (value) -> value
		| Var (value) -> State.eval st value
		| Binop (oper, expr1, expr2) ->
			let value1 = eval st expr1 
			and value2 = eval st expr2 
			in calc_bin oper value1 value2	


    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
	let ostap_list ops = 
    let ostap_bin oper = (ostap ($(oper)), fun x y -> Binop (oper, x, y)) 
	in List.map ostap_bin ops;;
	
    ostap (                                      
      (*parse: empty {failwith "Not implemented"}*)
	   primary:
         x:IDENT {Var x}
        | x:DECIMAL {Const x}
        | -"(" parse -")";
      parse:
        !(Ostap.Util.expr(fun x -> x)
          [|
            `Lefta, ostap_list ["!!"];
            `Lefta, ostap_list ["&&"];
            `Nona,  ostap_list [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, ostap_list ["+"; "-"];
            `Lefta, ostap_list ["*"; "/"; "%"]
          |]
          primary
        )
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    
    let eval env ((st, i, o) as conf) stmt = failwith "Not implemented"*)
	let rec eval env (s, i, o) st =
	match st with
	| Assign (x, expr) -> let value = Expr.eval s expr 
	in let st1 = State.update x value s 
	in (st1, i, o)
	| Read x -> 
		(match i with 
		| num :: t -> ((State.update x num s), t, o)
		| _ -> failwith "Input is empty!") 
	| Write expr -> (s, i, o @ [Expr.eval s expr])
	| Seq (l, r) -> eval env (eval env (s, i, o) l) r
	| Skip -> (s, i, o)
	| If (expr, l, r) -> if (Expr.eval s expr) != 0 then eval env (s, i, o) l else eval env (s, i, o) r
	| While (expr, stmt) -> if (Expr.eval s expr) != 0 then eval env (eval env (s, i, o) stmt) st else (s, i, o)
	| Repeat (expr, stmt) -> let (s', i', o') = eval env (s, i, o) stmt 
	in if Expr.eval s' expr == 0 then eval env (s', i', o') st  else (s', i', o')
	| Call (f, expr) -> let arg, locals, body = env#definition f
	in let rec zip = function
 	| x::xs, y::ys -> (x, y) :: zip (xs, ys)
	| [], [] -> []
	in let assign_arg st1 (x, expr) = State.update x (Expr.eval s expr) st1
	in let w_arg = List.fold_left assign_arg (State.enter s @@ arg @ locals) @@ zip (arg, expr)
	in let s', i, o = eval env (w_arg, i, o) body
	in State.leave s s', i, o
                                
    (* Statement parser *)
    ostap (
      (*parse: empty {failwith "Not implemented"}*)
	  parse: 
	  	l:stmt -";" r:parse { Seq (l, r) }
	  | stmt;
      stmt:  %"read" -"(" x:IDENT -")" { Read x }
           | %"write" -"(" expr:!(Expr.parse) -")" { Write expr }
           | x:IDENT -":=" expr:!(Expr.parse) { Assign (x, expr) }
		   | %"if" expr:!(Expr.parse) %"then" s:parse %"fi" {If (expr, s, Skip)}
		   | %"if" expr:!(Expr.parse) %"then" l:parse r:else_or_elif %"fi" {If (expr, l, r)}
		   | %"while" expr:!(Expr.parse) %"do" s:parse %"od" {While (expr, s)}
		   | %"for" condition:parse "," expr:!(Expr.parse) "," l:parse %"do" r:parse %"od" {Seq (condition, While (expr, Seq (r, l)))}
		   | %"repeat" s:parse %"until" expr:!(Expr.parse) {Repeat (expr, s)}
		   | %"skip" {Skip}
		   | x:IDENT "(" arg:!(Util.list0)[Expr.parse] ")" { Call (x, arg) };
		   else_or_elif: 
		     %"else" s:parse {s}
		   | %"elif" expr:!(Expr.parse) %"then" l:parse r:else_or_elif {If (expr, l, r)}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      (*parse: empty {failwith "Not implemented"}*)
	  argument: IDENT;
	  parse: 
	  	%"fun" fun_name:IDENT "(" arg: !(Util.list0 argument) ")"
		locals: (%"local" !(Util.list argument))?
		"{" body: !(Stmt.parse) "}" { (fun_name, (arg, (match locals with None -> [] | Some l -> l), body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream

let eval (defs, body) i = failwith "Not implemented"*)
let eval (defs, body) i = let module CustomMap = Map.Make (String) 
	in let definitionsMap = List.fold_left (fun f ((name, _) as definitions) -> CustomMap.add name definitions f) CustomMap.empty defs 
	in let env = (object method definition name = snd (CustomMap.find name definitionsMap) end) 
	in let _, _, o = Stmt.eval env (State.empty, i, []) body
	in o
                                   
(* Top-level parser 
let parse = failwith "Not implemented"*)
let parse = ostap (defs:!(Definition.parse)* body:!(Stmt.parse) {(defs, body)})