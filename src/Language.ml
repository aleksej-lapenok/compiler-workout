(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))
    | ".string"  -> let rec toString v = match v with
                    | (Value.Int n) -> string_of_int n
                    | (Value.String b) -> Printf.sprintf "\"%s\"" (Bytes.to_string b)
                    | (Value.Array elems) -> Printf.sprintf "[%s]" (String.concat ", " (List.map toString (Array.to_list elems)))
                    | (Value.Sexp (name, elems)) -> (match elems with
                                                    | [] -> Printf.sprintf "`%s" name
                                                    | _ ->  "`" ^ name ^ " (" ^ (String.concat ", " (List.map toString elems)) ^ ")"
                                                    )
                    in (st, i, o, Some (Value.String (Bytes.of_string (toString (List.hd args)))))
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
<<<<<<< HEAD
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    

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


     let rec eval env ((state, input, output, result) as conf) expr =  match expr with
       | Const a -> (state, input, output, Some (Value.of_int a))
       | Array exprs -> let (state', input', output', values) = eval_list env conf exprs in
                        env#definition env ".array" values (state, input', output', None)
       | String s -> (state, input, output, Some (Value.of_string (Bytes.of_string s)))
       | Sexp (name, exprs) -> let (state', input', output', values) = eval_list env conf exprs in
                               (state', input', output', Some (Value.Sexp (name, values)))
       | Var x -> (state, input, output, Some (State.eval state x))
       | Binop (op, x, y) -> let (state1, input1, output1, Some a1) = eval env (state, input, output, None) x in
                             let (state2, input2, output2, Some a2) = eval env (state1, input1, output1, None) y in
                             (state2, input2, output2, Some (Value.of_int (getFunction op (Value.to_int a1) (Value.to_int a2))))
       | Elem (arr_expr, idx_expr) -> let (state', input', output', values) = eval_list env conf [arr_expr; idx_expr] in
                                      env#definition env ".elem" values (state', input', output', None)
       | Length arr_expr -> let (state', input', output', Some arr) = eval env conf arr_expr in
                            env#definition env ".length" [arr] (state', input', output', None)
       | Call (f, args) -> let (state', input', output', values) = eval_list env conf args in
                           env#definition env f values (state', input', output', None)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
            let (_, _, _, Some v) as conf = eval env conf x in
            v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    let parseBinop op = ostap(- $(op)), (fun x y -> Binop(op, x, y))

    ostap (
      parse:
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
               arr_expr
           );
        arr_expr: idx:(
            a:indexed length: ".length"? { match length with
                                           | Some _ -> Length a
                                           | None -> a
                                          }
            )
            str:".string"? {match str with
                            | Some _ -> Call (".string", [idx])
                            | _ -> idx
                            };

        indexed: e:primary idx:inds {List.fold_left (fun e id -> Elem (e, id)) e idx};
        inds: idx:((-"[" parse -"]")*) {idx};

        primary: n:DECIMAL {Const n}
               | c:CHAR {Const (Char.code c)}
               | str: STRING {String (String.sub str 1 (String.length str - 2))}
               | f:IDENT "(" args:!(Util.list0 parse) ")" {Call (f, args)}
               | x:IDENT {Var x}
               | -"(" parse -")"
               | "[" exprs: !(Util.list0 parse) "]" {Array exprs}
               | "`" name:IDENT subs:((-"(" (!(Util.list)[parse]) -")")?) { match subs with
                                                                            | Some subs -> Sexp (name, subs)
                                                                            | _ -> Sexp (name, [])
                                                                           }
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse: wildcard | sexp | var ;

          wildcard: "_" {Wildcard};
          sexp: "`" name:IDENT subs_opt:((-"(" (!(Util.list)[parse])-")")?) { match subs_opt with
                                                                              | Some subs -> Sexp (name, subs)
                                                                              | _ -> Sexp (name, [])
                                                                            };
          var: name:IDENT {Ident name}
        )
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st


    let cont k stmt = match k with
     | Skip -> stmt
     | _ -> Seq (stmt, k)

     let isSome s = match s with
                    | Some _ -> true
                    | _ -> false

     let findCase value branches =
        let rec match_pattern value branch = match branch with
                                         | Pattern.Wildcard -> Some []
                                         | Pattern.Ident var -> Some [(var, value)]
                                         | Pattern.Sexp (name, subpatterns) -> let Value.Sexp (name', subvalues) = value in
                                                                              if ((name = name') && (List.length subpatterns = (List.length subvalues))) then
                                                                                 let subresults = List.map2 match_pattern subvalues subpatterns in
                                                                                 if (List.for_all isSome subresults) then
                                                                                    Some (List.concat (List.map (fun (Some lst) -> lst) subresults))
                                                                                 else
                                                                                     None
                                                                              else
                                                                                 None
        in let match_branch (pattern, stmt) = match (match_pattern value pattern) with
                                              | Some lst -> Some (lst, stmt)
                                              | None -> None
        in let Some (branch, stmt) = List.find isSome (List.map match_branch branches) in
        branch, stmt

     let rec eval env ((state, input, output, result) as conf) k stmt = match stmt with
(*        | Read x -> (match input with*)
(*                    | head :: tail -> eval env (State.update x head state, tail, output, None) Skip k*)
(*                    | _ -> failwith ("Empty input")*)
(*                    )*)
(*        | Write e -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) e in*)
(*                     eval env (state1, input1, output1 @ [value], None) Skip k*)
        | Assign (x, idxs, expr) -> let (state, input, output, idx) = Expr.eval_list env conf idxs in
                                    let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, None) expr in
                                    eval env (update state1 x value idx, input1, output1, Some value) Skip k
        | Seq (stmt1, stmt2) -> eval env (state, input, output, result) (cont k stmt2) stmt1
        | If (cond, thn, els) -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) cond in
                                 if Expr.toBool (Value.to_int value) then
                                     eval env (state1, input1, output1, None) k thn
                                 else
                                     eval env (state1, input1, output1, None) k els
        | While (cond, body) -> let (state1, input1, output1, Some value) = Expr.eval env (state, input, output, result) cond in
                                if not (Expr.toBool (Value.to_int value)) then
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
        | Case (expr, branches) -> let (state', input', output', Some value) = Expr.eval env (state, input, output, None) expr in
                                   let branch, stmt = findCase value branches in
                                   let branch_var_names, _ = List.split branch in
                                   let state = State.push state State.undefined branch_var_names in
                                   let state = List.fold_left (fun state (name, value) -> State.update name value state) state branch in
                                   let state, input, output, result = eval env (state, input, output, None) Skip stmt in
                                   let state = State.drop state in
                                   eval env (state, input, output, result) Skip k

    (* Statement parser *)
    ostap (
      line:
(*          "read"  "(" x:IDENT ")"          {Read x}*)
(*        | "write" "(" e:!(Expr.parse) ")"   {Write e}*)
          x:IDENT idx:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse)  {Assign (x, idx, e)}
        | "skip" {Skip}
        | "while" condition:!(Expr.parse) "do" body:parse "od" { While (condition, body)}
        | "for" init:!(parse) "," cond:!(Expr.parse) "," step:parse "do" body:parse "od"
            {
                Seq(init, While(cond, Seq(body, step)))
            }
        | "repeat" body:parse "until" cond:!(Expr.parse)
            {
                Repeat (body, cond)
            }
        | "skip" {Skip}
        | "if" i:ifParse {i}
        | name:IDENT "(" args:!(Util.list0 Expr.parse) ")" {Call (name, args)}
        | "return" expr:!(Expr.parse)? {Return expr}
        | "case" value:!(Expr.parse) "of" branches:(!(Util.listBy)[ostap ("|")][case_branch]) "esac" {Case (value, branches)}
        ;

       ifParse: condition:!(Expr.parse) "then" stmt1:parse stmt2:elseParse {If (condition, stmt1, stmt2) }
      ;

       elseParse:  "fi" {Skip}
        | "else" stmt:parse "fi" {stmt}
        | "elif" i:ifParse {i}
        ;

        case_branch: p:!(Pattern.parse) "->" stmt:parse {(p, stmt)};

       parse: l:line ";" rest:parse {Seq (l, rest)} | line
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
