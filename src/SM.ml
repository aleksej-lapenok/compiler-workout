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
 with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                                                  
let rec eval env (stack, (state, configInput, configOutput)) program = 
  match program with 
  | [] -> (stack, (state, configInput, configOutput))
  | prg::rest -> 
      let evalCode cfg = eval env cfg rest in
      let evalJmp cfg label = eval env cfg (env#labeled label) in
      match prg with
        | BINOP op -> evalCode (match stack with
                       | y::x::tail -> ([Language.Expr.getFunction op x y] @ tail, (state, configInput, configOutput))
                       | _ -> failwith "Not enouth values on stack for BINOP"
                       )
        | CONST n -> evalCode ([n] @ stack, (state, configInput, configOutput))
        | READ -> evalCode (match configInput with
                  | head :: tail -> ([head] @ stack, (state, tail, configOutput))
                  | _ -> failwith "Can't read from inputStream"
                  )
        | WRITE -> evalCode (match stack with 
                   | head :: tail -> (tail, (state, configInput, configOutput @ [head]))
                   | _ -> failwith "Not enouth values on stack for WRITE"
                   )
        | LD x -> evalCode ([state x] @ stack, (state, configInput, configOutput))
        | ST x -> evalCode (match stack with 
                  | head::tail -> (tail, (Language.Expr.update x head state, configInput, configOutput))
                  | _ -> failwith "Not enouth values on stack for ST"
                  )
        | JMP l -> evalJmp (stack, (state, configInput, configOutput)) l
        | LABEL _ -> evalCode (stack, (state, configInput, configOutput))
        | CJMP (c, l) -> (match stack with 
                          | head :: tails-> if (c = "z" && head = 0) || (c = "nz" && head != 0) then
                                               evalJmp (tails, (state, configInput, configOutput)) l
                                            else
                                                evalCode (stack, (state, configInput, configOutput))
                          | _ -> failwith "Not enough values on stack for CJMP"
                         ) 


class labels = 
  object(self)
    val labelCount = 0

     method getLabel = ".L" ^ string_of_int labelCount, {< labelCount = labelCount + 1 >}
  end


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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine

*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
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
  | Stmt.Read x        -> env, [READ; ST x]
  | Stmt.Write e       -> env, expr e @ [WRITE]
  | Stmt.Assign (x, e) -> env, expr e @ [ST x]
  | Stmt.If (c, t, e)  -> let outLabel, env = env#getLabel in
                          let env, code     = if_stmt env outLabel @@ Stmt.If (c, t, e) in
                          env, code @ [LABEL outLabel]
  | Stmt.Skip          -> env, []
  | Stmt.While (c, b)  -> let bodyLabel, env = env#getLabel in
                          let condLabel, env = env#getLabel in
                          let env, body      = stmt env b   in
                          env, [JMP condLabel;LABEL bodyLabel] @ body @ [LABEL condLabel] @ expr c @ [CJMP ("nz", bodyLabel)]
  | Stmt.Repeat (b, c) -> let bodyLabel, env = env#getLabel in
                          let env, body      = stmt env b in
                          env, [LABEL bodyLabel] @ body @ expr c @ [CJMP ("z", bodyLabel)]
  in function
  code -> snd @@ stmt (new labels) code
(*
let rec compileRow expr = match expr with
  | Language.Expr.Const n -> [CONST n]
  | Language.Expr.Var x -> [LD x]
  | Language.Expr.Binop (op, a, b) -> (compileRow a) @ (compileRow b) @ [BINOP op]


let rec compile stmt = match stmt with
  | Language.Stmt.Read x -> [READ; ST x]
  | Language.Stmt.Write e -> (compileRow e) @ [WRITE]
  | Language.Stmt.Assign (x, e) -> (compileRow e) @ [ST x]
  | Language.Stmt.Seq (stmt1, stmt2) -> (compile stmt1) @ (compile stmt2)
*)
