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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
                        
let rec eval env conf prog = failwith "Not yet implemented"*)

let rec eval env (st, (s, i, o)) = function
	| [] -> st, (s, i, o)    
	| instr :: tail -> 
		match instr with
		| BINOP bin -> 
			(match st with 
				  y :: x :: t_end -> eval env ((Expr.calc_bin bin x y) :: t_end, (s, i ,o))) tail
		| CONST v -> eval env (v :: st, (s, i, o)) tail
		| READ -> let num = List.hd i in eval env (num :: st, (s, List.tl i, o)) tail
		| WRITE -> let num = List.hd st in eval env (List.tl st, (s, i, o @ [num])) tail
		| LD x -> eval env ((s x) :: st, (s, i, o)) tail
		| ST x -> let num = List.hd st in eval env (List.tl st, (Expr.update x num s, i, o)) tail
		| LABEL _ -> eval env (st, (s, i, o)) tail
		| JMP nm -> eval env (st, (s, i, o)) (env#labeled nm)
		| CJMP (condition, nm) -> 
		let value::st' = st in
		let x = match condition with
		| "nz" -> value <> 0
		| "z" -> value = 0 in
		eval env (st', (s, i, o)) (if (x) then (env#labeled nm) else tail)
		


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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine

let compile p = failwith "Not yet implemented"*)

let env = object
    val mutable count = 0
    method l_new = count <- (count + 1); "L" ^ string_of_int count
  end 

let rec compile =
	let rec ex_comp = function
	| Expr.Const v -> [CONST v]
	| Expr.Var v -> [LD v]
	| Expr.Binop (oper, expr1, expr2) -> (ex_comp expr1) @ (ex_comp expr2) @ [BINOP oper]
	in
	function
	| Stmt.Assign (x, expr) -> (ex_comp expr) @ [ST x]
    | Stmt.Read x ->  [READ; ST x]
    | Stmt.Write expr -> (ex_comp expr) @ [WRITE]
    | Stmt.Seq (l, r) -> (compile l) @ (compile r)
	| Stmt.Skip -> []
	| Stmt.If (expr, l, r) -> 
	let l_else = env#l_new in
	let l_end = env#l_new in
	let curr = compile l in
	let last = compile r in
	(ex_comp expr @ [CJMP ("z", l_else)] @ curr @ [JMP l_end] @ [LABEL l_else] @ last @ [LABEL l_end])
	| Stmt.While (expr, st) ->
	let l_end = env#l_new in
	let l_loop = env#l_new in
	let body = compile st in
	([JMP l_end] @ [LABEL l_loop] @ body @ [LABEL l_end] @ ex_comp expr @ [CJMP ("nz", l_loop)])
	| Stmt.Repeat (expr, st) ->
	let l_loop = env#l_new in
	let body = compile st in 
	([LABEL l_loop] @ body @ ex_comp expr @ [CJMP ("z", l_loop)])