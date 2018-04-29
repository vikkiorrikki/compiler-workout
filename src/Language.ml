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

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
                                                        
    let rec eval env ((st, i, o, r) as conf) expr = failwith "Not implemented"*)
	
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
	
	let rec eval env ((s, i, o, r) as conf) expr =
		match expr with
		| Const (value) -> (s, i, o, Some value)
		| Var (value) -> 
			let v = State.eval s value 
			in (s, i, o, Some v)
		| Binop (oper, expr1, expr2) ->
			let (s', i', o', Some f_arg) = eval env conf expr1
			in let (s', i', o', Some s_arg) = eval env (s', i', o', Some f_arg) expr2 
			in let rv = calc_bin oper f_arg s_arg in 
			(s', i', o', Some rv)
		| Call (nm, arg) -> 
			let rec c_args env conf arg = 
			match arg with
			| e::arg' ->
				let (s', i', o', Some c_arg) as conf' = eval env conf e 
				in let c_args, conf' = c_args env conf' arg'
				in c_arg::c_args, conf'
			| [] -> [], conf
			in let c_args', conf' = c_args env conf arg
			in env#definition env nm c_args' conf'
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      (*parse: empty {failwith "Not implemented"}*)
	  primary:
          x:IDENT "(" arg:!(Util.list0)[parse] ")" {Call (x, arg)} 
		| x:IDENT {Var x}
        | x:DECIMAL {Const x}
        | -"(" parse -")";
      parse:
        !(Ostap.Util.expr(fun x -> x)
		(Array.map (fun(a, s) -> a, List.map (fun s -> ostap (- $(s)), (fun x y -> Binop (s, x, y))) s)
          [|
            `Lefta, ["!!"];
            `Lefta, ["&&"];
            `Nona,  [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, ["+"; "-"];
            `Lefta, ["*"; "/"; "%"]
          |]
		  )
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    
    let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemnted"*)
	let rec eval env conf k stmt =
		let diam stmt k = 
			if k = Skip then stmt
			else Seq (stmt, k)
		in
		match conf, stmt with
		| (s, i, o, r), Assign (x, expr) -> 
			let (s', i', o', Some value) = Expr.eval env conf expr 
			in eval env (State.update x value s', i', o', r) Skip k
		| (s, z::i, o, r), Read x -> eval env (State.update x z s, i, o, r) Skip k
		| (s, i, o, r), Write expr -> let (s', i', o', Some value) = 
			Expr.eval env conf expr
			in eval env (s', i', o' @ [value], r) Skip k
		| conf, Seq (l, r) -> eval env conf (diam r k) l
		| conf, Skip -> if k = Skip then conf else eval env conf Skip k
		| (s, i, o, r), If (expr, l', r') -> let (s', i', o', Some value) =
			Expr.eval env conf expr
			in let a v = if v == 0 then r' else l'
			in eval env (s', i', o', Some value) k (a value)
		| conf, While (expr, l_stmt) -> let (s', i', o', Some value) =
			Expr.eval env conf expr
			in if value == 0 then eval env (s', i', o', Some value) Skip k 
			else eval env (s', i', o', Some value) (diam stmt k) l_stmt
		| conf, Repeat (expr, l_stmt) -> eval env conf (diam (While(Expr.Binop ("==", expr, Expr.Const 0), l_stmt)) k) l_stmt
		| (s, i, o, r), Call (nm, arg) -> 
			let rec c_args env conf arg = 
			match arg with
			| e::arg' -> let (s', i', o', Some c_arg) as conf' =
				Expr.eval env conf e
				in let c_args', conf' = c_args env conf' arg'
				in c_arg::c_args', conf'
			| [] -> [], conf
			in let c_args, conf' = c_args env conf arg
			in let c' = env#definition env nm c_args conf'
			in eval env c' Skip k
		| (s, i, o, r), Return expr ->
			(match expr with
				| None -> (s, i, o, None)
				| Some expr -> Expr.eval env conf expr )
         
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
		   | x:IDENT "(" arg:!(Util.list0)[Expr.parse] ")" { Call (x, arg) }
		   | %"return" expr:!(Expr.parse)? {Return expr};
		   else_or_elif: 
		     %"else" s:parse {s}
		   | %"elif" expr:!(Expr.parse) %"then" l:parse r:else_or_elif {If (expr, l, r)}
		   | "" {Skip}
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (     
      (*parse: empty {failwith "Not implemented"}*)
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))