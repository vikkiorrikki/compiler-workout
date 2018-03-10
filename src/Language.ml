(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT
open Ostap

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

		let rec eval st expr = 
			match expr with
			| Const (value) -> value
			| Var (value) -> st value
			| Binop (oper, expr1, expr2) ->
				let value1 = eval st expr1 
				and value2 = eval st expr2 
				in calc_bin oper value1 value2	

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    
    let eval _ = failwith "Not implemented yet"*)
	
	let ostap_list ops = 
    	let ostap_bin oper = (ostap ($(oper)), fun x y -> Binop (oper, x, y)) in 
    	List.map ostap_bin ops

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)
    ostap (
      (*parse: empty {failwith "Not implemented yet"}*)
	  primary:
         x:IDENT {Var x}
        | x:DECIMAL {Const x}
        | -"(" parse -")";
      parse:
        !(Util.expr(fun x -> x)
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    
    let eval _ = failwith "Not implemented yet"*)
	
	let rec eval ((s, i, o) : config) st =
        match st with
		| Assign (x, expr) -> ((Expr.update x (Expr.eval s expr) s), i, o)
        | Read x -> 
            (match i with 
            | num :: t -> ((Expr.update x num s), t, o)
			|[] -> failwith "Input is empty!") 
        | Write expr -> (s, i, o @ [(Expr.eval s expr)])
        | Seq (l, r) -> 
            let tmp1 = eval (s, i, o) l in
			eval tmp1 r

    (* Statement parser *)
    ostap (
      (*parse: empty {failwith "Not implemented yet"}*)
	  parse: 
	  	seq | st;
      seq: 
	  	l:st -";" r:parse { Seq (l, r) };
      st:  "read" -"(" x:IDENT -")" { Read x }
           | "write" -"(" expr:!(Expr.parse) -")" { Write expr }
           | x:IDENT -":=" expr:!(Expr.parse) { Assign (x, expr) }
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