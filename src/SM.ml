open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)      
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
unzip ([], l) n

(*let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented"*)
let rec eval env conf prg = 
	match prg with  
	| [] -> conf
	| instr::tail -> 
		let (cstack, st, conf') = conf
		in let (s, i, o) = conf'
		in match instr with
		| BINOP bin -> let (x::y::t_tail) = st
			in eval env (cstack, (Value.of_int (Expr.calc_bin bin (Value.to_int y) (Value.to_int x)))::t_tail, conf') tail
		| CONST v -> eval env (cstack, (Value.of_int v)::st, conf') tail
		| STRING str -> eval env (cstack, (Value.of_string str)::st, conf') tail
		| LD x -> eval env (cstack, (State.eval s x)::st, conf') tail
		| ST x -> let (s'::t_tail) = st in eval env (cstack, t_tail, ((State.update x s' s), i, o)) tail
		| STA (value, n) -> let v::ind, st' = split (n + 1) st
			in eval env (cstack, st', (Language.Stmt.update s value v (List.rev ind), i, o)) tail
		| LABEL _ -> eval env conf tail
		| JMP l -> eval env conf (env#labeled l)
		| CJMP (condition, nm) -> let (s::t_tail) = st in let x = 
			match condition with
			| "nz" -> Value.to_int s <> 0 
			| "z" -> Value.to_int s == 0 
			in eval env (cstack, t_tail, conf') (if (x) then (env#labeled nm) else tail )
		| CALL (f, n, x) -> if env#is_label f then eval env ((tail, s)::cstack, st, conf') (env#labeled f) else eval env (env#builtin conf f n x) tail
		| BEGIN (_, arg, xs) -> let rec get_args s = function
			| a::arg, z::st -> let s', st' = get_args s (arg, st)
			in State.update a z s', st'
			| [], st -> s, st
		in let s', st' = get_args (State.enter s @@ arg @ xs) (arg, st)
		in eval env (cstack, st', (s', i, o)) tail
		| END | RET _ ->
		match cstack with
		| (prog, s')::cstack' -> eval env (cstack', st, (State.leave s s', i, o)) prog
		| [] -> conf

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine

let compile (defs, p) = failwith "Not implemented"*)
let env = object
    val mutable count = 0
    method l_new = count <- (count + 1); "L" ^ string_of_int count
end
  
let rec ex_comp expr =
	match expr with
	| Expr.Const v -> [CONST v]
	| Expr.Var v -> [LD v]
	| Expr.String str -> [STRING str]
  	| Expr.Array array -> List.flatten (List.map ex_comp array) @ [CALL ("$array", List.length array, false)]
  	| Expr.Elem (array, i) -> ex_comp array @ ex_comp i @ [CALL ("$elem", 2, false)]
	| Expr.Length v -> ex_comp v @ [CALL ("$length", 1, false)]
	| Expr.Binop (oper, expr1, expr2) -> (ex_comp expr1) @ (ex_comp expr2) @ [BINOP oper]
	| Expr.Call (nm, arg) -> List.fold_left (fun ac e -> ex_comp e @ ac) [] arg @ [CALL ("L" ^ nm, List.length arg, false)]

let compile (defs, p) =
	let rec compile' p =
	match p with
	| Stmt.Assign (x, [], expr) -> (ex_comp expr) @ [ST x]
	| Stmt.Assign (x, ind, expr) -> List.flatten (List.map ex_comp (ind @ [expr])) @ [STA (x, List.length ind)]
	| Stmt.Seq (l, r) -> (compile' l) @ (compile' r)
	| Stmt.Skip -> []
	| Stmt.If (expr, l, r) -> 
		let l_else = env#l_new 
		in let l_end = env#l_new 
		in let curr = compile' l
		in let last = compile' r
		in ex_comp expr @ [CJMP ("z", l_else)] @ curr @ [JMP l_end] @ [LABEL l_else] @ last @ [LABEL l_end]
	| Stmt.While (expr, st) ->
		let l_end = env#l_new 
		in let l_loop = env#l_new 
		in let body = compile' st
		in [JMP l_end] @ [LABEL l_loop] @ body @ [LABEL l_end] @ ex_comp expr @ [CJMP ("nz", l_loop)]
	| Stmt.Repeat (expr, st) ->
		let l_loop = env#l_new 
		in let body = compile' st
		in [LABEL l_loop] @ body @ ex_comp expr @ [CJMP ("z", l_loop)]
	| Stmt.Return expr -> 
		(match expr with
		| None -> [RET false]
		| Some expr -> ex_comp expr @ [RET true] )
		| Stmt.Call (nm, arg) ->
			List.concat (List.map ex_comp arg) @ [CALL ("L" ^ nm, List.length arg, true)]
			in let comp_d (nm, (arg, locals, body)) = [LABEL ("L" ^ nm); BEGIN (nm, arg, locals)] @ compile' body @ [END] 
			in (compile' p @ [END] @ List.concat (List.map comp_d defs))