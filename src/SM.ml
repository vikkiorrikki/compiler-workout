open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
                                             
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented"*)
let rec eval env conf prg = 
	match prg with   
	| instr :: tail -> (
		match conf, instr with
		| (cstack, y::x::st, conf'), BINOP bin -> 
			let value = Expr.calc_bin bin x y
			in eval env (cstack, value :: st, conf') tail
		| (cstack, st, conf'), CONST v -> eval env (cstack, v :: st, conf') tail
		| (cstack, st, (s, z::i, o)), READ -> eval env (cstack, z :: st, (s, i, o)) tail
		| (cstack, z::st, (s, i, o)), WRITE -> eval env (cstack, st, (s, i, o @ [z])) tail
		| (cstack, st, (s, i, o)), LD x -> let value = State.eval s x in eval env (cstack, value :: st, (s, i, o)) tail
		| (cstack, z::st, (s, i, o)), ST x -> let s' = State.update x z s in eval env (cstack, st, (s', i, o)) tail
		| conf, LABEL l -> eval env conf tail
		| conf, JMP l -> eval env conf (env#labeled l)
		| (cstack, z :: st, conf'), CJMP (condition, nm) -> 
			(match condition with
			| "z" -> if z == 0 then eval env (cstack, st, conf') (env#labeled nm) else eval env (cstack, st, conf') tail
			| "nz" -> if z <> 0 then eval env (cstack, st, conf') (env#labeled nm) else eval env (cstack, st, conf') tail )
		| (cstack, st, (s, i, o)), CALL (f, _, _) -> eval env ((tail, s)::cstack, st, (s, i, o)) (env#labeled f)
		| (cstack, st, (s, i, o)), BEGIN (_, arg, xs) -> let rec get_args s arg st = 
			match arg, st with
			| a::arg', z::st' -> let s', _st = get_args s arg' st'
			in (State.update a z s', _st)
			| [], st' -> (s, st')
		in let s', st' = get_args (State.enter s (arg @ xs)) arg st
		in eval env (cstack, st', (s', i, o)) tail
		| (cstack, st, (s, i, o)), END | (cstack, st, (s, i, o)), RET _ ->
		(match cstack with
		| (prog, s')::cstack' -> eval env (cstack', st, (State.leave s s', i, o)) prog
		| [] -> conf)
	)
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine

let compile (defs, p) = failwith "Not implemented"*)
let env = object
    val count = 0
    method l_new = "LABEL" ^ string_of_int count, {< count = (count + 1) >}
  end 

let rec ex_comp expr =
	match expr with
	| Expr.Const v -> [CONST v]
	| Expr.Var v -> [LD v]
	| Expr.Binop (oper, expr1, expr2) -> (ex_comp expr1) @ (ex_comp expr2) @ [BINOP oper]
	| Expr.Call (nm, arg) -> List.concat (List.map ex_comp (List.rev arg)) @ [CALL (nm, List.length arg, false)]

let rec compile' stmt env =
	match stmt with
	| Stmt.Assign (x, expr) -> (ex_comp expr) @ [ST x], env
	| Stmt.Read x ->  [READ; ST x], env
	| Stmt.Write expr -> (ex_comp expr) @ [WRITE], env
	| Stmt.Seq (l, r) -> 
		let left, env = compile' l env
		in let right, env = compile' r env 
		in left @ right, env
	| Stmt.Skip -> [], env
	| Stmt.If (expr, l, r) -> 
		let l_else, env = env#l_new 
		in let l_end, env = env#l_new 
		in let curr, env = compile' l env 
		in let last, env = compile' r env
		in ex_comp expr @ [CJMP ("z", l_else)] @ curr @ [JMP l_end] @ [LABEL l_else] @ last @ [LABEL l_end], env
	| Stmt.While (expr, st) ->
		let l_end, env = env#l_new 
		in let l_loop, env = env#l_new 
		in let body, env = compile' st env
		in [JMP l_end] @ [LABEL l_loop] @ body @ [LABEL l_end] @ ex_comp expr @ [CJMP ("nz", l_loop)], env
	| Stmt.Repeat (expr, st) ->
		let l_loop, env = env#l_new 
		in let body, env = compile' st env
		in [LABEL l_loop] @ body @ ex_comp expr @ [CJMP ("z", l_loop)], env
	| Stmt.Call (nm, arg) ->
		List.concat (List.map ex_comp (List.rev arg)) @ [CALL (nm, List.length arg, true)], env
	| Stmt.Return expr -> 
		match expr with
		| None -> [RET false], env
		| Some expr -> ex_comp expr @ [RET true], env
		
let compile (defs, stmt) = 
	let prog, env = compile' stmt env
	in let rec compile_def env defs = 
	match defs with
	| (name, (arg, locals, body))::defs' ->
		let b_defs, env = compile_def env defs'
		in let c_body, env = compile' body env 
		in [LABEL name; BEGIN (name, arg, locals)] @ c_body @ [END] @ b_defs, env
	| [] -> [], env
	in let c_def, _ = compile_def env defs 
	in prog @ [END] @ c_def
