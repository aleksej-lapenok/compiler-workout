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
 *)                         
(*
let eval cfg prg = List.fold_left evalRow cfg prg
*)

let evalRow (stack, (state, cfgInput, cfgOutput))  prg = match prg with
  | BINOP op -> (match stack with
                 | y::x::tail -> ([Syntax.Expr.getFunction op x y] @ tail, (state, cfgInput, cfgOutput))
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
            | head::tail -> (tail, (Syntax.Expr.update x head state, cfgInput, cfgOutput))
            | _ -> failwith "Not enouth values on stack for ST"
            )

let eval cfg prg = List.fold_left evalRow cfg prg
(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compileRow expr = match expr with
  | Syntax.Expr.Const n -> [CONST n]
  | Syntax.Expr.Var x -> [LD x]
  | Syntax.Expr.Binop (op, a, b) -> (compileRow a) @ (compileRow b) @ [BINOP op]


let rec compile stmt = match stmt with
  | Syntax.Stmt.Read x -> [READ; ST x]
  | Syntax.Stmt.Write e -> (compileRow e) @ [WRITE]
  | Syntax.Stmt.Assign (x, e) -> (compileRow e) @ [ST x]
  | Syntax.Stmt.Seq (stmt1, stmt2) -> (compile stmt1) @ (compile stmt2)
