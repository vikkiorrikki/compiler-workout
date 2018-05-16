(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a
	
	let tag_of = function
    | Sexp (t, _) -> t
	| _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
	let init_list n f = 
		let rec init i n f = 
			if i >= n then [] else (f i) :: (init (i + 1) n f) 
			in init 0 n f
    let update_array  a i x = init_list   (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
                                                           
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op) *)
  let int_to_bool x = 
		if x == 0 then false else true
	let bool_to_int op_bool =
		if op_bool then 1 else 0
		
	let rec calc_bin bin x y = 
		match bin with
		| "+" -> x + y
		| "-" -> x - y
		| "*" -> x * y
		| "/" -> x / y
		| "%" -> x mod y
		| "<" -> bool_to_int (x < y)
		| "<=" -> bool_to_int (x <= y)
		| ">" -> bool_to_int (x > y)
		| ">=" -> bool_to_int (x >= y)
		| "==" -> bool_to_int (x == y)
		| "!=" -> bool_to_int (x <> y)
		| "&&" -> bool_to_int (int_to_bool x && int_to_bool y)
		| "!!" -> bool_to_int (int_to_bool x || int_to_bool y)
		| _ -> failwith ("Unknown op")
    
    (*let rec eval env ((st, i, o, r) as conf) expr = failwith "Not implemented"*)
	let rec eval env ((s, i, o, r) as conf) expr =
		match expr with
		| Const (value) -> (s, i, o, Some (Value.of_int value))
		| Var value -> let v = State.eval s value
			in (s, i, o, Some v)
		| Binop (oper, expr1, expr2) ->
			let (_, _, _, Some f_arg) as conf' = eval env conf expr1
			in let (s', i', o', Some s_arg) = eval env conf' expr2 
			in (s', i', o', Some (Value.of_int (calc_bin oper (Value.to_int f_arg) (Value.to_int s_arg))))
		| String str -> (s, i, o, Some (Value.of_string str))
    	| Array (array) -> let (s, i, o, vs) = eval_list env conf array 
			in env#definition env ".array" vs (s, i, o, None)
		| Sexp (t, xs) -> let (s, i, o, vs) = eval_list env conf xs
			in (s, i, o, Some(Value.Sexp (t, vs)))
		| Elem (x, i) -> let (s, i, o, args) = eval_list env conf [x; i]  
      		in env#definition env ".elem" args (s, i, o, None)
    	| Length (str) -> let (s, i, o, Some v) = eval env conf str
			in env#definition env ".length" [v] (s, i, o, None)
		| Call (nm, arg) -> (let c_args, conf' = List.fold_left ( fun (acc, conf) e -> let (_, _, _, Some v) as conf' = eval env conf e in v::acc, conf'
			) ([], conf) arg
			in env#definition env nm (List.rev c_args) conf'
			)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
	  
	let obinopList op_list = 
      let obinop oper = (ostap ($(oper)), fun x y -> Binop (oper, x, y)) in 
		List.map obinop op_list;; 
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      (*parse: empty {failwith "Not implemented"}*)
	  parse: 
        !(Util.expr
          (fun x -> x)
          [|
            `Lefta, obinopList ["!!"];
            `Lefta, obinopList ["&&"];
            `Nona,  obinopList [">="; ">"; "<="; "<"; "=="; "!="];
            `Lefta, obinopList ["+"; "-"];
            `Lefta, obinopList ["*"; "/"; "%"]
          |]
          primary
        );
      primary: b:base is:(-"[" i:parse -"]" {`Elem i} | "." %"length" {`Len}) * {List.fold_left (fun x -> function `Elem i -> Elem (x, i) | `Len -> Length x) b is};
      base:
        n:DECIMAL {Const n}
        | s:STRING {String (String.sub s 1 (String.length s - 2))}
        | c:CHAR {Const (Char.code c)}
        | "[" es:!(Util.list0)[parse] "]" {Array es}
        | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match args with None -> [] | Some args -> args)}
        | x:IDENT s: ("(" args: !(Util.list0)[parse] ")" {Call (x, args)} | empty {Var x}) {s}
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          (*parse: empty {failwith "Not implemented"}*)
		  parse: "_" {Wildcard}
		  | "`" t: IDENT par: (-"(" !(Util.list)[parse] - ")")? {Sexp (t, match par with None -> [] | Some par -> par)}
		  | x: IDENT {Ident x}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    (*let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemented"*)
	let rec eval env ((s, i, o, r) as conf) k stmt =
		match stmt with
		| Assign (x, ind, expr) -> 
			let (s, i, o, ind) = Expr.eval_list env conf ind
			in let (s, i, o, Some value) = Expr.eval env (s, i, o, None) expr
			in eval env (update s x value ind, i, o, None) Skip k
		| Seq (l, r) -> eval env conf ( match k with
				| Skip -> r
				| _ -> Seq (r, k)) l
		| Skip -> (match k with
			| Skip -> conf
			| _ -> eval env conf Skip k)
		| If (expr, l', r') -> let (s', i', o', Some v) =
			Expr.eval env conf expr
			in eval env conf k (if Value.to_int v <> 0 then l' else r')
		| While (expr, l_stmt) -> eval env conf k (If (expr, Seq (l_stmt, While (expr, l_stmt)), Skip))
		| Repeat (expr, l_stmt) -> eval env conf k (Seq (l_stmt, If (expr, Skip, Repeat (expr, l_stmt))))
		| Call (nm, arg) -> eval env (Expr.eval env conf (Expr.Call (nm, arg))) Skip k
		| Leave -> eval env (State.drop s, i, o, r) Skip k
		| Case (ex, b) -> let (_, _, _, Some v) as conf' = Expr.eval env conf ex 
			in let rec br ((s, i, o, _) as conf) = function
          	| [] -> failwith("No branch selected!")
          	| (patt, body)::tl -> let rec m_patt patt v s = let update x v = function
              | None -> None
              | Some _s -> Some (State.bind x v _s)
              in match patt, v with
              | Pattern.Ident x, v -> update x v s
              | Pattern.Wildcard, _ -> s
              | Pattern.Sexp (t, xs), Value.Sexp (t', vs) when t = t' -> m_list xs vs s
              | _ -> None
            and m_list xs vs _s = match xs, vs with
              | [], [] -> _s
              | p::xs, v::vs -> m_list xs vs (m_patt p v _s)
              | _ -> None
            in match m_patt patt v (Some State.undefined) with
            | None -> br conf tl
            | Some s' -> eval env (State.push s s' (Pattern.vars patt), i, o, None) k (Seq (body, Leave))
          	in br conf' b
		| Return expr ->
			(match expr with
				| None -> conf
				| Some expr -> Expr.eval env conf expr );;
                                                        
    (* Statement parser *)
    ostap (
      (*parse: empty {failwith "Not implemented"}*)
	   parse: seq | stmt;
      stmt: assign | if_ | while_ | for_ | repeat_ | skip | call | return | case;
      assign: x:IDENT index:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) { Assign (x, index, e) };
      if_: "if" e:!(Expr.parse) "then" s:parse "fi" {If (e, s, Skip)} 
         | "if" e:!(Expr.parse) "then" s1:parse else_elif:else_or_elif "fi" {If (e, s1, else_elif)};
      else_or_elif: else_ | elif_;
      else_: "else" s:parse {s};
      elif_: "elif" e:!(Expr.parse) "then" s1:parse s2:else_or_elif {If (e, s1, s2)};
      while_: "while" e:!(Expr.parse) "do" s:parse "od" {While (e, s)};
      for_: "for" init:parse "," e:!(Expr.parse) "," s1:parse "do" s2:parse "od" {Seq (init, While (e, Seq(s2, s1)))};
      repeat_: "repeat" s:parse "until" e:!(Expr.parse) {Repeat (e, s)};
      skip: "skip" {Skip};
      call: x:IDENT "(" args:!(Util.list0)[Expr.parse] ")" {Call (x, args)};
      return: "return" e:!(Expr.parse)? {Return e};
		seq: l_st:stmt -";" r_st:parse { Seq (l_st, r_st) };	
	  case: "case" e:!(Expr.parse) "of" branches: !(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)] "esac" {Case (e, branches)}
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
