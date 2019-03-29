(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let fromBool b = if b then 1 else 0

    let toBool b = b <> 0 

    let ($) f1 f2 a b = f2 (f1 a b)

    let getFunction op = match op with 
       | "+" -> (+)
       | "-" -> (-)
       | "*" -> ( * )
       | "/" -> (/)
       | "%" -> (mod)
       | "<" -> (<) $ fromBool
       | "<=" -> (<=) $ fromBool
       | ">" -> (>) $ fromBool
       | ">=" -> (>=) $ fromBool
       | "==" -> (=) $ fromBool
       | "!=" -> (<>) $ fromBool 
       | "&&" -> fun x y -> fromBool ((&&) (toBool x) (toBool y)) 
       | "!!" -> fun x y -> fromBool ((||) (toBool x) (toBool y))
       | _ -> raise Not_found

    let rec eval state expr =  match expr with
       | Const a -> a
       | Var x -> state x
       | Binop (op, x, y) -> (getFunction op) 
            (eval state x) (eval state y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let parseBinop op = ostap(- $(op)), (fun x y -> Binop(op, x, y))

    ostap (
      expr: 
           !(Ostap.Util.expr
                 (fun x -> x)
                 (Array.map (fun (assoc, ops) -> assoc, List.map parseBinop ops)
                  [|
                     `Lefta, ["!!"];
                     `Lefta, ["&&"];
                     `Nona, ["<="; "<"; ">="; ">"; "=="; "!="];
                     `Lefta, ["+"; "-"];
                     `Lefta, ["*"; "/"; "%"];
                  |]
                 )
                 primary
             );
      primary: n:DECIMAL {Const n} | x:IDENT {Var x} | -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)

    (* Statement parser *)
    (*ostap (
      parse: empty {failwith "Not yet implemented"}
 
          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    )
*)
    let rec eval (state, input, output) stmt = match stmt with
        | Read x -> (match input with
                    | head :: tail -> (Expr.update x head state, tail, output)
                    | _ -> failwith ("Empty input")
                    )
        | Write e -> (state, input, output @ [Expr.eval state e])
        | Assign (x, e) -> (Expr.update x (Expr.eval state e) state, input, output)
        | Seq (stmt1, stmt2) -> eval (eval (state, input, output) stmt1) stmt2 
        | If (cond, thn, els) -> if Expr.toBool (Expr.eval state cond) then
                                     eval (state, input, output) thn
                                 else 
                                     eval (state, input, output) els
        | While (cond, body) -> if not (Expr.toBool (Expr.eval state cond)) then 
                                   (state, input, output)
                                else  
                                   eval (eval (state, input, output) body) @@ stmt
        | Repeat (body, cond) -> let conf' = eval (state, input, output) body in
                                      let (state', _, _) = conf' in
                                      if Expr.toBool (Expr.eval state' cond) then
                                           conf'
                                      else 
                                          eval conf' stmt
        | Skip -> (state, input, output)

    (* Statement parser *)
    ostap (
      line: 
          "read"  "(" x:IDENT ")"          {Read x}
        | "write" "(" e:!(Expr.expr) ")"   {Write e}
        | x:IDENT ":=" e:!(Expr.expr)     {Assign (x, e)}
        | "while" condition:!(Expr.expr) "do" body:parse "od" { While (condition, body)}
        | "for" init:!(parse) "," cond:!(Expr.expr) "," step:parse "do" body:parse "od"
            {
                Seq(init, While(cond, Seq(body, step)))
            }
        | "repeat" body:parse "until" cond:!(Expr.expr)
            { 
                Repeat (body, cond)
            }
        | "skip" {Skip}
        | "if" i:ifParse {i}
        ;

      ifParse: condition:!(Expr.expr) "then" stmt1:parse stmt2:elseParse {If (condition, stmt1, stmt2) }
      ;

      elseParse:  "fi" {Skip}
        | "else" stmt:parse "fi" {stmt}
        | "elif" i:ifParse {i}
        ;
 
        parse: l:line ";" rest:parse {Seq (l, rest)} | line
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
