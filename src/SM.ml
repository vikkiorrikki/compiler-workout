open GT

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
                         
let eval _ = failwith "Not yet implemented"*)

let rec eval conf prog = 
    let conf_upd instr ((st, (s, i, o)) : config) = 
		match instr with
		| BINOP bin -> 
			(match st with 
				  y :: x :: t_end -> ((Syntax.Expr.calc_bin bin x y) :: t_end, (s, i ,o))) 
		| CONST v -> (v :: st, (s, i, o))
		| READ -> let num = List.hd i in (num :: st, (s, List.tl i, o))
		| WRITE -> let num = List.hd st in (List.tl st, (s, i, o @ [num]))
		| LD x -> ((s x) :: st, (s, i, o))
		| ST x -> let num = List.hd st in (List.tl st, (Syntax.Expr.update x num s, i, o)) in
	match prog with
	| [] -> conf    
	| instr :: tail -> 
		eval (conf_upd instr conf) tail;;

let rec ex_comp (exp : Syntax.Expr.t) = 
	match exp with
	| Syntax.Expr.Const v -> [CONST v]
	| Syntax.Expr.Var v -> [LD v]
	| Syntax.Expr.Binop (oper, expr1, expr2) -> (ex_comp expr1) @ (ex_comp expr2) @ [BINOP oper];;

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 

let compile _ = failwith "Not yet implemented"*)

let rec comp (st : Syntax.Stmt.t) =
    match st with
	| Syntax.Stmt.Assign (x, expr) -> (ex_comp expr) @ [ST x]
    | Syntax.Stmt.Read x ->  [READ; ST x]
    | Syntax.Stmt.Write expr -> (ex_comp expr) @ [WRITE]
    | Syntax.Stmt.Seq (l, r) -> (comp l) @ (comp r)