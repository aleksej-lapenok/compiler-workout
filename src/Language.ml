(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
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

    let rec eval env (state, input, output, _) expr =  match expr with
       | Const a -> (state, input, output, Some a)
       | Var x -> (state, input, output, Some (State.eval state x))
       | Binop (op, x, y) -> let (state1, input1, output1, Some a1) = eval env (state, input, output, None) x in
                             let (state2, input2, output2, Some a2) = eval env (state1, input1, output1, None) y in
                             (state2, input2, output2, Some (getFunction op a1 a2))
       | Call (f, args) -> (let eval_arg (state, input, output, values) arg = let (state1, input1, output1, Some value) = eval env (state, input, output, None) arg in
                                                                             (state1, input1, output1, values @ [value]) in
                           let state1, input1, output1, values = List.fold_left eval_arg (state, input, output, []) args in
                           env#definition env f values (state1, input1, output1, None)

       )

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
      primary: n:DECIMAL {Const n}
             | f:IDENT "(" args:!(Util.list0 expr) ")" {Call (f, args)}
             | x:IDENT {Var x}
             | -"(" expr -")"

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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let cont k stmt = match k with
    | Skip -> stmt
    | _ -> Seq (stmt, k)

    let rec eval env ((state, input, output, result) as conf) k stmt = match stmt with
        | Read x -> (match input with
                    | head :: tail -> eval env (State.update x head state, tail, output, None) Skip k
                    | _ -> failwith ("Empty input")
                    )
        | Write e -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) e in
                     eval env (state1, input1, output1 @ [value], None) Skip k
        | Assign (x, e) -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) e in
                           eval env (State.update x value state1, input1, output1, Some value) Skip k
        | Seq (stmt1, stmt2) -> eval env (state, input, output, result) (cont k stmt2) stmt1
        | If (cond, thn, els) -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) cond in
                                 if Expr.toBool value then
                                     eval env (state1, input1, output1, None) k thn
                                 else
                                     eval env (state1, input1, output1, None) k els
        | While (cond, body) -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) cond in
                                if not (Expr.toBool value) then
                                   eval env (state1, input1, output1, None) Skip k
                                else
                                   eval env (state1, input1, output1, None) (cont k stmt) body
        | Repeat (body, cond) -> eval env (state, input, output, result) (cont k (While (Expr.Binop ("==", cond, Expr.Const 0), body))) body
        | Skip -> (match k with
                  | Skip -> conf
                  | _ -> eval env conf Skip k
                  )
        | Call (name, args) -> eval env (Expr.eval env (state, input, output, result) (Expr.Call (name, args))) Skip k
        | Return res -> (match res with
                          | Some expr -> Expr.eval env (state, input, output, result) expr
                          | _ -> (state, input, output, None)
                        )
    (* Statement parser *)
    ostap (
      line:
          "read"  "(" x:IDENT ")"          {Read x}
        | "write" "(" e:!(Expr.expr) ")"   {Write e}
        | x:IDENT ":=" e:!(Expr.expr)     {Assign (x, e)}
        | "skip" {Skip}
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
        | name:IDENT "(" args:!(Expr.expr)* ")" {Call (name, args)}
        | "return" expr:!(Expr.expr)? {Return expr}
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

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
          arg: IDENT;
          parse: "fun" name:IDENT "(" args:!(Util.list0 arg) ")" local: (%"local" local:!(Util.list0 arg))? "{" body:!(Stmt.parse) "}" {
            let l = (match local with
            | Some v -> v
            | _ -> []
            ) in
            name, (args, l, body)
          }
        )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
