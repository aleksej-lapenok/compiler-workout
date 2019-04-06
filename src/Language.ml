(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
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
           | Var x -> State.eval state x
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (state, input, output) stmt = match stmt with
            | Read x -> (match input with
                        | head :: tail -> (State.update x head state, tail, output)
                        | _ -> failwith ("Empty input")
                        )
            | Write e -> (state, input, output @ [Expr.eval state e])
            | Assign (x, e) -> (State.update x (Expr.eval state e) state, input, output)
            | Seq (stmt1, stmt2) -> eval env (eval env (state, input, output) stmt1) stmt2
            | If (cond, thn, els) -> if Expr.toBool (Expr.eval state cond) then
                                         eval env (state, input, output) thn
                                     else
                                         eval env (state, input, output) els
            | While (cond, body) -> if not (Expr.toBool (Expr.eval state cond)) then
                                       (state, input, output)
                                    else
                                       eval env (eval env (state, input, output) body) @@ stmt
            | Repeat (body, cond) -> let conf' = eval env (state, input, output) body in
                                          let (state', _, _) = conf' in
                                          if Expr.toBool (Expr.eval state' cond) then
                                               conf'
                                          else
                                              eval env conf' stmt
            | Skip -> (state, input, output)
            | Call (name, args) -> let (names, localVars, body) = env#definition name in
                                   let args = List.combine names @@ List.map (Expr.eval state) args in
                                   let stateWithScope = State.push_scope state (names @ localVars) in
                                   let updtateState s (name, value) = State.update name value s in
                                   let functionState = List.fold_left updtateState stateWithScope args in
                                   let (state', input', output') = eval env (functionState, input, output) body in
                                   (State.drop_scope state' state, input', output')

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
            | name:IDENT "(" args:!(Expr.expr)* ")" {Call (name, args)}
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
      parse: "fun" name:IDENT "(" args:IDENT* ")" local: (%"local" IDENT*)? "{" body:!(Stmt.parse) "}" {
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
