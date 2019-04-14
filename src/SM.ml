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
        
let rec eval env ((functionStack, stack, (state, configInput, configOutput) as stmtConfig) as cfg) program =
  match program with
  | [] -> (functionStack, stack, (state, configInput, configOutput))
  | prg::rest -> match prg with
        | LABEL _ -> eval env cfg rest
        | BINOP op -> eval env (match stack with
                       | y::x::tail -> (functionStack, Language.Value.of_int (Language.Expr.getFunction op (Language.Value.to_int x) (Language.Value.to_int y)) :: tail, (state, configInput, configOutput))
                       | _ -> failwith "Not enouth values on stack for BINOP"
                       ) rest
        | CONST n -> eval env (functionStack, [Language.Value.of_int n] @ stack, (state, configInput, configOutput)) rest
        | STRING s -> eval env (functionStack, (Language.Value.of_string s)::stack, (state, configInput, configOutput)) rest
(*        | READ -> eval env (match configInput with*)
(*                  | head :: tail -> (functionStack, [head] @ stack, (state, tail, configOutput))*)
(*                  | _ -> failwith "Can't read from inputStream"*)
(*                  ) rest*)
(*        | WRITE -> eval env (match stack with*)
(*                   | head :: tail -> (functionStack, tail, (state, configInput, configOutput @ [head]))*)
(*                   | _ -> failwith "Not enouth values on stack for WRITE"*)
(*                   ) rest*)
        | LD x -> eval env (functionStack, Language.State.eval state x :: stack, (state, configInput, configOutput)) rest
        | ST x -> eval env (match stack with
                  | head::tail -> (functionStack, tail, (Language.State.update x head state, configInput, configOutput))
                  | _ -> failwith "Not enouth values on stack for ST"
                  ) rest
        | STA (x, size) -> let (value::ids), tail = split (size + 1) stack in
                           eval env (functionStack, tail, (Language.Stmt.update state x value ids, configInput, configOutput)) rest
        | JMP l -> eval env cfg (env#labeled l)
        | CJMP (c, l) -> (match stack with
                          | head :: tails-> if (c = "z" && (Language.Value.to_int head) = 0) || (c = "nz" && (Language.Value.to_int head) != 0) then
                                               eval env (functionStack, tails, (state, configInput, configOutput)) (env#labeled l)
                                            else
                                               eval env (functionStack, tails, (state, configInput, configOutput)) rest
                          | _ -> failwith "Not enough values on stack for CJMP"
                         )
        | BEGIN (n, a, loc) -> let scope = State.enter state (a@loc) in
                               let state', stack' = List.fold_left (fun (s, value::tail) name -> (State.update name value s, tail)) (scope, stack) a in
                               eval env (functionStack, stack', (state', configInput, configOutput)) rest
        | CALL (f, args_count, is_function) -> if env#is_label f then
                                eval env ((rest, state) :: functionStack, stack, (state, configInput, configOutput)) (env#labeled f)
                            else
                                eval env (env#builtin (functionStack, stack, (state, configInput, configOutput)) f args_count (not is_function)) rest
        | (RET _ | END) -> match functionStack with
                            | (rest, state') :: tail -> eval env (tail, stack, (State.leave state state', configInput, configOutput)) rest
                            | _ -> (functionStack, stack, (state, configInput, configOutput))
        | _ -> failwith "this comand"

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
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) args f in
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
class labels =
  object(self)
    val labelCount = 0

      method getLabel = ".L" ^ string_of_int labelCount, {< labelCount = labelCount + 1 >}
  end


 let rec compileStmt env code =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Array exprs      -> let compiledExprs = List.flatten (List.map (expr) (List.rev exprs)) in
                             compiledExprs @ [CALL ("$array", (List.length compiledExprs), true)]
  | Expr.String s         -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Elem (arr, idx)  -> expr idx @ expr arr @ [CALL ("$elem", 2, true)]
  | Expr.Length arr       -> expr arr @ [CALL ("$length", 1, true)]
  | Expr.Call (f, args) -> let cArgs = List.concat (List.map expr (List.rev args)) in
                           cArgs @ [CALL (f, List.length args, true)]
  in
  let rec stmt env =
     let rec if_stmt env outLabel = function
        | Stmt.Seq (s1, s2)  -> let env, code = stmt env s1 in
                                let env, code' = if_stmt env outLabel s2 in
                                env, code @ code'
        | Stmt.If (c, t, e) -> let elseLabel, env = env#getLabel in
                               let env, thenBody = if_stmt env outLabel t in
                               let env, elseBody = stmt env e in
                               env, expr c @ [CJMP ("z", elseLabel)] @ thenBody @ [JMP outLabel; LABEL elseLabel] @ elseBody
        | other -> stmt env other in function
          | Stmt.Seq (s1, s2) -> let env, code = stmt env s1 in
                                 let env, code' = stmt env s2 in
                                 env, code @ code'
(*          | Stmt.Read x        -> env, [READ; ST x]*)
(*          | Stmt.Write e       -> env, expr e @ [WRITE]*)
          | Stmt.Assign (x, idx, e) -> (match idx with
                                        | [] -> env, expr e @ [ST x]
                                        | idx -> let compiledIdx = List.fold_left (fun comp e -> comp @ (expr e)) [] (List.rev idx) in
                                                 env, compiledIdx @ expr e @ [STA (x, List.length idx)]
                                        )
          | Stmt.If (c, t, e)  -> let outLabel, env = env#getLabel in
                                  let env, code     = if_stmt env outLabel @@ Stmt.If (c, t, e) in
                                  env, code @ [LABEL outLabel]
          | Stmt.Skip          -> env, []
          | Stmt.While (c, b)  -> let bodyLabel, env = env#getLabel in
                                  let condLabel, env = env#getLabel in
                                  let env, body      = stmt env b   in
                                  env, [JMP condLabel; LABEL bodyLabel] @ body @ [LABEL condLabel] @ expr c @ [CJMP ("nz", bodyLabel)]
          | Stmt.Repeat (b, c) -> let bodyLabel, env = env#getLabel in
                                  let env, body      = stmt env b in
                                  env, [LABEL bodyLabel] @ body @ expr c @ [CJMP ("z", bodyLabel)]
          | Stmt.Call (f, a) -> env, List.concat (List.map expr (List.rev a)) @ [CALL (f, List.length a, false)]
          | Stmt.Return e    -> (match e with
                                  | Some v -> env, (expr v) @ [RET true]
                                  | _ -> env, [RET false]
                                )
          in stmt env code

 let rec compile (defs, main) =
    let compileDef (name, (args, localVars, body)) env =
        let env, compiledBody = compileStmt env body in
        env, [LABEL name] @ [BEGIN (name, args, localVars)] @ compiledBody @ [END] in
    let rec compileDefs defs env = (match defs with
                                   | head :: tail -> let env, newHead = compileDef head env in
                                                     newHead @ compileDefs tail env
                                   | _ -> []
                                   ) in
    let env, compiledMain = compileStmt (new labels) main in
    let compiledDefs = compileDefs defs env in
    compiledMain @ [END] @ compiledDefs