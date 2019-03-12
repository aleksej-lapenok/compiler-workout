open GT       
open Language
       
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
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
*)                                                  
let evalRow (stack, (state, cfgInput, cfgOutput))  prg = match prg with
  | BINOP op -> (match stack with
                 | y::x::tail -> ([Language.Expr.getFunction op x y] @ tail, (state, cfgInput, cfgOutput))
                 | _ -> failwith "Not enouth values on stack for BINOP"
                 )
  | CONST n -> ([n] @ stack, (state, cfgInput, cfgOutput))
  | READ -> (match cfgInput with
            | head :: tail -> ([head] @ stack, (state, tail, cfgOutput))
            | _ -> failwith "Can't read from inputStream"
            )
  | WRITE -> (match stack with 
             | head :: tail -> (tail, (state, cfgInput, cfgOutput @ [head]))
             | _ -> failwith "Not enouth values on stack for WRITE"
             )
  | LD x -> ([state x] @ stack, (state, cfgInput, cfgOutput))
  | ST x -> (match stack with 
            | head::tail -> (tail, (Language.Expr.update x head state, cfgInput, cfgOutput))
            | _ -> failwith "Not enouth values on stack for ST"
            )

let eval cfg prg = List.fold_left evalRow cfg prg

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

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
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
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
