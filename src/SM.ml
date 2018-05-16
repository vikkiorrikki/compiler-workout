open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
          
(*let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) _ = failwith "Not yet implemented"*)
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
		| SEXP (x, v) -> let ex, r = split v st in eval env (cstack, (Value.sexp x (List.rev ex)) :: r, conf') tail
		| LABEL _ -> eval env conf tail
		| JMP l -> eval env conf (env#labeled l)
		| CJMP (condition, nm) -> let (s::t_tail) = st in let x = 
			match condition with
			| "nz" -> Value.to_int s <> 0 
			| "z" -> Value.to_int s == 0 
			in eval env (cstack, t_tail, conf') (if (x) then (env#labeled nm) else tail )
		| CALL (f, n, x) -> if env#is_label f then eval env ((tail, s)::cstack, st, conf') (env#labeled f) else eval env (env#builtin conf f n x) tail
		| BEGIN (_, arg, xs) -> let ns = State.enter s (arg @ xs)
			in let arg', st' = split (List.length arg) st
			in let s' = List.fold_left2 (fun ast p v -> State.update p v ast) ns arg (List.rev arg')
		in eval env (cstack, st', (s', i, o)) tail
		| DROP -> eval env (cstack, List.tl st, conf') tail
      	| DUP -> eval env (cstack, List.hd st::st, conf') tail
      	| SWAP -> let x::y::t_tail = st in eval env (cstack, y::x::t_tail, conf') tail
      	| TAG l -> let x::t_tail = st in let res = if l = Value.tag_of x then 1 else 0
        	in eval env (cstack, (Value.of_int res)::t_tail, conf') tail
      	| ENTER xs -> let vals, st' = split (List.length xs) st 
			in let s' = List.fold_left2 (fun _s x v -> State.bind v x _s) State.undefined vals xs 
			in eval env (cstack, st', (State.push s s' xs, i, o)) tail
		| LEAVE -> eval env (cstack, st, (State.drop s, i, o)) tail
		| END | RET _ ->
		match cstack with
		| (prog, _s)::cstack' -> eval env (cstack', st, (State.leave s _s, i, o)) prog
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
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    (*args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse _ = failwith "Not implemented"
  and bindings p = failwith "Not implemented"
  and expr e = failwith "Not implemented" in
  let rec compile_stmt l env stmt =  failwith "Not implemented" in*)
  args_code @ [CALL (f, List.length args, p)]
    and pattern p lfalse =
    (let rec comp patt = (match patt with
        Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [DROP]
      | Stmt.Pattern.Sexp (tag, ps) -> let res, _ = (List.fold_left (fun (acc, pos) patt -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp patt)), pos + 1) ([], 0) ps) in
        [DUP; TAG tag; CJMP ("z", lfalse)] @ res) in comp p)
  and bindings p =
    let rec bind cp = 
      (match cp with
        Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [SWAP]
      | Stmt.Pattern.Sexp (_, xs) -> let res, _ = List.fold_left (fun (acc, pos) curp -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)) ([], 0) xs in res @ [DROP]) in
	bind p @ [ENTER (Stmt.Pattern.vars p)]
and expr e = match e with
	| Expr.Const v -> [CONST v]
	| Expr.Var v -> [LD v]
	| Expr.String str -> [STRING str]
  	| Expr.Array array -> List.flatten (List.map expr array) @ [CALL (".array", List.length array, false)]
  	| Expr.Elem (array, i) -> expr array @ expr i @ [CALL (".elem", 2, false)]
	| Expr.Length v -> expr v @ [CALL (".length", 1, false)]
	| Expr.Binop (oper, expr1, expr2) -> (expr expr1) @ (expr expr2) @ [BINOP oper]
	| Expr.Sexp (s, ex) -> let args = List.fold_left (fun acc ind -> acc @ (expr ind)) [] ex in args @ [SEXP (s, List.length ex)]
	| Expr.Call (nm, arg) -> call (label nm) arg false
in let rec compile' l env stmt =
	match stmt with
	| Stmt.Assign (x, [], ex) -> env, false, expr ex @ [ST x]
	| Stmt.Assign (x, ind, ex) -> let id = List.fold_left (fun acc index -> acc @ (expr index)) [] ind
		in env, false, (List.rev id @ expr ex @ [STA (x, List.length ind)])
	| Stmt.Seq (left, right) -> let env, _, l' = compile' l env left 
		in let env, _, r' = compile' l env right 
		in env, false, l' @ r'
	| Stmt.Skip -> env, false, []
	| Stmt.If (ex, left, right) -> 
		let l_else, env = env#get_label 
		in let l_end, env = env#get_label 
		in let env, _, curr = compile' l env left
		in let env, _, last = compile' l env right
		in env, false, (expr ex) @ [CJMP ("z", l_else)] @ curr @ [JMP l_end] @ [LABEL l_else] @ last @ [LABEL l_end]
	| Stmt.While (ex, st) ->
		let l_end, env = env#get_label 
		in let l_loop, env = env#get_label 
		in let env, _, body = compile' l env st
		in env, false, [JMP l_end] @ [LABEL l_loop] @ body @ [LABEL l_end] @ expr ex @ [CJMP ("nz", l_loop)]
	| Stmt.Repeat (ex, st) ->
		let l_loop, env = env#get_label 
		in let env, _, body = compile' l env st
		in env, false, [LABEL l_loop] @ body @ expr ex @ [CJMP ("z", l_loop)]
	| Stmt.Return ex -> 
		(match ex with
		| None -> env, false, [RET false]
		| Some ex -> env, false, expr ex @ [RET true] )
		| Stmt.Call (nm, arg) -> env, false, List.concat (List.map expr arg) @ [CALL ("L" ^ nm, List.length arg, true)]
	| Stmt.Case (ex, patterns) -> let rec comp_pat ps env lbl isFirst lend = 
      (match ps with
        [] -> env, []
        | (p, act)::tl -> 
          let env, _, body = compile' l env act 
          in let lfalse, env = env#get_label and start = if isFirst then [] else [LABEL lbl]
          in let env, code = comp_pat tl env lfalse false lend
          in env, start @ (pattern p lfalse) @ bindings p @ body @ [LEAVE; JMP lend] @ code)
      in let lend, env = env#get_label
      in let env, code = comp_pat patterns env "" true lend
      in env, false, (expr ex) @ code @ [LABEL lend]
	| Stmt.Leave -> env, false, [LEAVE] in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile' lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile' lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 