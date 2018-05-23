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
		(match conf, instr with
		| (cstack, y::x::st, tconf'), BINOP bin -> 
			let value = Language.Expr.calc_bin bin(Value.to_int x) (Value.to_int y)
			in eval env (cstack, (Value.of_int value)::st, tconf') tail
		| (cstack, st, tconf'), CONST v -> eval env (cstack, (Value.of_int v)::st, tconf') tail
		| (cstack, st, sconf'), STRING str -> eval env (cstack, (Value.of_string str)::st, sconf') tail
		| (cstack, st, sconf'), SEXP (x, v) -> let ex, st' = split v st in eval env (cstack, (Value.sexp x (List.rev ex))::st', sconf') tail
		| (cstack, st, (s, i, o)), LD x -> eval env (cstack, (State.eval s x)::st, (s, i, o)) tail
		| (cstack, z::st, (s, i, o)), ST x ->  eval env (cstack, st, (State.update x z s, i, o)) tail
		| (cstack, st, (s, i, o)), STA (value, n) -> let v::ind, st' = split (n + 1) st
			in eval env (cstack, st', (Language.Stmt.update s value v (List.rev ind), i, o)) tail
		| conf, LABEL l -> eval env conf tail
		| conf, JMP l -> eval env conf (env#labeled l)
		| (cstack, z :: st, tconf'), CJMP (condition, nm) -> 
			(match condition with
			| "z" -> if Value.to_int z == 0 then eval env (cstack, st, tconf') (env#labeled nm) else eval env (cstack, st, tconf') tail
			| "nz" -> if Value.to_int z <> 0 then eval env (cstack, st, tconf') (env#labeled nm) else eval env (cstack, st, tconf') tail 
			| _ -> failwith("undefined suf!"))
		| (cstack, st, (s, i, o)), CALL (f, n, x) -> if env#is_label f then eval env ((tail, s)::cstack, st, (s, i, o)) (env#labeled f) else eval env (env#builtin conf f n x) tail
		| (cstack, st, (s, i, o)), BEGIN (_, arg, xs) -> let ns = State.enter s (arg @ xs)
			in let arg', rs = split (List.length arg) st
			in let s' = List.fold_left2 (fun ast p v -> State.update p v ast) ns arg (List.rev arg')
		in eval env (cstack, rs, (s', i, o)) tail
		| (cstack, st, (s, i, o)), END | (cstack, st, (s, i, o)), RET _ ->
			(match cstack with
			| (prog, s')::cstack' -> eval env (cstack', st, (State.leave s s', i, o)) prog
			| [] -> conf)
		| (cstack, z::st, sconf'), DROP -> eval env (cstack, st, sconf') tail
      	| (cstack, z::st, sconf'), DUP -> eval env (cstack, z::z::st, sconf') tail
      	| (cstack, x::y::st, sconf'), SWAP -> eval env (cstack, y::x::st, sconf') tail
      	| (cstack, sexp::st, sconf'), TAG l -> let res = if l = Value.tag_of sexp then 1 else 0
        	in eval env (cstack, (Value.of_int res)::st, sconf') tail
      	| (cstack, st, (s, i, o)), ENTER xs -> let vals, rs = split (List.length xs) st 
			in let s' = List.fold_left2 (fun ast e var -> State.bind var e ast) State.undefined vals xs 
			in eval env (cstack, rs, (State.push s s' xs, i, o)) tail
		| (cstack, st, (s, i, o)), LEAVE -> eval env (cstack, st, (State.drop s, i, o)) tail)

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
    and pattern lfalse = function
      | Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident _ -> [DROP]
      | Stmt.Pattern.Sexp (tag, ps) -> [DUP; TAG tag; CJMP ("z", lfalse)] @ List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ pattern lfalse x) ps)
	  | _ -> [JMP lfalse]
  and bindings p =
    let rec bind = function
      | Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [SWAP]
      | Stmt.Pattern.Sexp (_, xs) -> List.concat (List.mapi (fun i x -> [DUP; CONST i; CALL (".elem", 2, false)] @ bind x) xs) @ [DROP]
in bind p @ [ENTER (Stmt.Pattern.vars p)]
and expr e = match e with
	| Expr.Const v -> [CONST v]
	| Expr.Var v -> [LD v]
	| Expr.String str -> [STRING str]
	| Expr.Sexp (s, ex) -> (List.concat (List.map expr ex)) @ [SEXP (s, List.length ex)]
  	| Expr.Array array -> call ".array" array false
  	| Expr.Elem (array, i) -> call ".elem" [array; i] false
	| Expr.Length expr -> call ".length" [expr] false
	| Expr.Binop (oper, expr1, expr2) -> expr expr1 @ expr expr2 @ [BINOP oper]
	| Expr.Call (nm, arg) -> call (label nm) (List.rev arg) false
in let rec compile' l env stmt =
	match stmt with
	| Stmt.Assign (x, [], ex) -> env, false, expr ex @ [ST x]
	| Stmt.Assign (x, ind, ex) -> let id = List.concat (List.map expr (ind @ [ex])) @ [STA (x, List.length ind)]
		in env, false, id
	| Stmt.Seq (left, right) -> let env, _, l' = compile' l env left 
		in let env, _, r' = compile' l env right 
		in env, false, l' @ r'
	| Stmt.Skip -> env, false, []
	| Stmt.If (ex, left, right) -> 
		let l_else, env = env#get_label 
		in let l_end, env = env#get_label 
		in let env, _, curr = compile' l env left
		in let env, _, last = compile' l env right
		in env, false, (expr ex) @ [CJMP ("z", l_else)] @ curr @ [JMP l_end; LABEL l_else] @ last @ [LABEL l_end]
	| Stmt.While (ex, st) ->
		let l_end, env = env#get_label 
		in let l_loop, env = env#get_label 
		in let env, _, wbody = compile' l env st
		in env, false, [JMP l_end; LABEL l_loop] @ wbody @ [LABEL l_end] @ expr ex @ [CJMP ("nz", l_loop)]
	| Stmt.Repeat (ex, st) ->
		(let l_loop, env = env#get_label 
		in let env, _, rbody = compile' l env st
		in env, false, [LABEL l_loop] @ rbody @ expr ex @ [CJMP ("z", l_loop)])
	| Stmt.Call (nm, arg) -> env, false, call (label nm) (List.rev arg) true
	| Stmt.Leave -> env, false, [LEAVE]
	| Stmt.Case (ex, bs) -> (let lend, env = env#get_label
		in let rec comp_pat ps env lbl n = 
      (match ps with
        [] -> env, []
        | (p, body)::tl -> 
          let env, _, body_comp = compile' l env body 
          in let lfalse, env = if n = 0 then lend, env else env#get_label
          in let env, code = comp_pat tl env (Some lfalse) (n - 1)
		  in env, (match lbl with
		  None -> []
		  | Some l -> [LABEL l]) @ (pattern lfalse p) @ bindings p @ body_comp @ [LEAVE] @ (if n = 0 then [] else [JMP lend]) @ code)
      in let env, code = comp_pat bs env None (List.length bs - 1)
      in env, false, expr ex @ code @ [LABEL lend])
	| Stmt.Return ex -> 
		(match ex with
		| None -> env, false, [RET false]
		| Some ex -> env, false, expr ex @ [RET true] )
	 in
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