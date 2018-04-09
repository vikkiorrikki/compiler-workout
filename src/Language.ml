(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
                                                         
    let eval st expr = failwith "Not yet implemented"*)
	
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
		| Var (value) -> st value
		| Binop (oper, expr1, expr2) ->
			let value1 = eval st expr1 
			and value2 = eval st expr2 
			in calc_bin oper value1 value2	

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
	
	let ostap_list ops = 
    let ostap_bin oper = (ostap ($(oper)), fun x y -> Binop (oper, x, y)) in 
	List.map ostap_bin ops;;

    ostap (                                      
      (*parse: empty {failwith "Not yet implemented"}*)
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
    (* loop with a post-condition       *) | Repeat of Expr.t * t with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    
    let rec eval conf stmt = failwith "Not yet implemented"*)
	let rec eval (s, i, o) st =
	match st with
	| Assign (x, expr) -> ((Expr.update x (Expr.eval s expr) s), i, o)
	| Read x -> 
		(match i with 
		| num :: t -> ((Expr.update x num s), t, o)
		| _ -> failwith "Input is empty!") 
	| Write expr -> (s, i, o @ [(Expr.eval s expr)])
	| Seq (l, r) -> 
		let tmp1 = eval (s, i, o) l in
		eval tmp1 r
	| Skip -> (s, i, o)
	| If (expr, l, r) -> if (Expr.eval s expr) != 0 then eval (s, i, o) l else eval (s, i, o) r
	| While (expr, stmt) -> if (Expr.eval s expr) != 0 then eval (eval (s, i, o) stmt) st else (s, i, o)
	| Repeat (expr, stmt) -> let (s', i', o') = eval (s, i, o) stmt in 
	if Expr.eval s' expr == 0 then eval (s', i', o') st  else (s', i', o')
                               
    (* Statement parser *)
    ostap (
      (*parse: empty {failwith "Not yet implemented"}*)
	parse: 
	  seq | stmt;
      seq: 
	  	l:stmt -";" r:parse { Seq (l, r) }
	  | stmt;
      stmt:  %"read" -"(" x:IDENT -")" { Read x }
           | %"write" -"(" expr:!(Expr.parse) -")" { Write expr }
           | x:IDENT -":=" expr:!(Expr.parse) { Assign (x, expr) }
		   | %"skip" {Skip}
		   | %"if" expr:!(Expr.parse) %"then" s:parse %"fi" {If (expr, s, Skip)}
		   | %"if" expr:!(Expr.parse) %"then" l:parse r:else_or_elif %"fi" {If (expr, l, r)}
		   | %"while" expr:!(Expr.parse) %"do" s:parse %"od" {While (expr, s)}
		   | %"for" condition:parse "," expr:!(Expr.parse) "," l:parse %"do" r:parse %"od" {Seq (condition, While (expr, Seq (r, l)))}
		   | %"repeat" s:parse %"until" expr:!(Expr.parse) {Repeat (expr, s)}
		   | %"skip" {Skip};
		   else_or_elif: 
		     %"else" s:parse {s}
		   | %"elif" expr:!(Expr.parse) %"then" l:parse r:else_or_elif {If (expr, l, r)}
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
